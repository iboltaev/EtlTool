import org.apache.calcite.sql.{SqlAsOperator, SqlBasicCall, SqlCall, SqlDialect, SqlIdentifier, SqlJoin, SqlNode, SqlNodeList, SqlSelect, SqlTableRef, SqlWindow, SqlWith, SqlWithItem}
import org.apache.calcite.sql.parser.SqlParser.Config
import org.apache.calcite.sql.parser.SqlParserPos
import org.checkerframework.checker.nullness.qual.Nullable

import java.io.Reader
import scala.collection.JavaConversions._
import scala.collection.JavaConverters._
import scala.collection.immutable.TreeMap

sealed trait Pipe {
  def name: String
}

case class Join(name: String , left: String, right: String , typ: String, cond: SqlNode) extends Pipe
case class Group(name: String = "") extends Pipe
case class Wnd(name: String = "") extends Pipe
case class ProjFilter(name: String = "") extends Pipe
case class TableSrc(name: String = "", alias: String = "") extends Pipe

case class JoinTable(name: String, sql: SqlNode)

object Main extends App {

  lazy val parser = org.apache.calcite.sql.parser.SqlParser.create(Reader.nullReader(), Config.DEFAULT)

  /*
  1. subquery in 'join'
  2. more than 1 joins
  3. group by
  4. window functions
   */

  private def rewriteFromWithCTES(node: SqlNode, ctes: Set[String], prefix: String = ""): Unit = node match {
    case i: SqlIdentifier =>
      if (i.names.length == 1 ) {
        val nm = i.names(0)
        val key = s"${prefix}_${nm}"
        if (ctes.contains(key))
          i.setNames(Seq(key).asJava, Seq(SqlParserPos.ZERO).asJava)
      }
    case c: SqlCall =>
      c.getOperandList.foreach { op =>
        rewriteFromWithCTES(op, ctes, prefix)
      }
    case _ =>
      ()
  }

  private def rewriteBodyWithCTES(node: SqlNode, ctes: Set[String], prefix: String = ""): Unit = node match {
    case s: SqlSelect =>
      rewriteFromWithCTES(s, ctes, prefix)
    case c: SqlCall =>
      c.getOperandList.foreach { o =>
        rewriteBodyWithCTES(o, ctes, prefix)
      }
    case _ =>
      ()
  }

  private def tryExtractCTEs(node: SqlNode, prefix: String = "cte"): TreeMap[String, SqlNode] = node match {
    case w: SqlWith =>
      val ctes = w.withList.iterator().map(_.asInstanceOf[SqlWithItem]).flatMap { item =>
        val nm = item.name.names.mkString(".")
        val subtree = tryExtractCTEs(item.query, s"${prefix}_${nm}")
        subtree.insert(s"${prefix}_${nm}", item.query)
      }.toMap

      rewriteBodyWithCTES(w.body, ctes.keySet, prefix)
      val all = ctes + (prefix -> w.body)
      TreeMap(all.toSeq: _*)
    case c: SqlCall =>
      TreeMap(
        Option(c.getOperandList).toIndexedSeq.flatMap(_.toIndexedSeq).filter(_ != null).flatMap(n => tryExtractCTEs(n, prefix)): _*
      )
    case _ =>
      TreeMap.empty
  }

  // 1. First stage - split query with CTEs to own queries, rewriting aliases
  def extractCTEs(node: SqlNode, prefix: String = "cte"): TreeMap[String, SqlNode] = {
    val result = tryExtractCTEs(node, prefix)
    if (result.isEmpty) TreeMap((prefix -> node))
    else result
  }

  // 2. Second stage - extract subqueries to own queries, rewriting references with aliases
  def extractSubqueries(node: SqlNode, counter: Int = 0, parent: SqlNode = null): TreeMap[String, SqlNode] = node match {
    case s: SqlSelect =>
      // parent is 'AS' node with 2 childs: SqlSelect and alias
      if (parent != null && parent.isInstanceOf[SqlCall]) {
        val bc = parent.asInstanceOf[SqlCall]
        val childIdx = bc.getOperandList.indexOf(s)
        if (childIdx >= 0) {
          bc.setOperand(childIdx, new SqlIdentifier(Seq(s"sq_${counter}").asJava, SqlParserPos.ZERO))
        }
      }
      val from = extractSubqueries(s.getFrom, counter + 1, s)
      val where = extractSubqueries(s.getWhere, from.size, s)
      (from ++ where).insert(s"sq_${counter}", s)
    case c: SqlCall =>
      TreeMap(
        Option(c.getOperandList).toIndexedSeq.flatMap(_.toIndexedSeq).filter(_ != null).flatMap(n => extractSubqueries(n, counter, c)): _*
      )
    case _ =>
      TreeMap.empty
  }

  private def foldMaps(it: Iterable[TreeMap[String, Set[String]]]): TreeMap[String, Set[String]] = it.foldLeft(TreeMap.empty[String, Set[String]]) { (res, tm) =>
    tm.foldLeft(res) { (res, pair) =>
      val ex = res.getOrElse(pair._1, Set.empty[String])
      res.updated(pair._1, ex ++ pair._2)
    }
  }

  private def extractFields(node: SqlNode): TreeMap[String, Set[String]] = node match {
    case s: SqlSelect =>
      foldMaps(Seq(
        foldMaps(s.getSelectList.map(extractFields)),
        if (s.getFrom.isInstanceOf[SqlJoin]) extractFields(s.getFrom) else TreeMap.empty,
        extractFields(s.getWhere)
      ))
    case w: SqlWindow =>
      foldMaps(Option(w.getOperandList).toSeq.flatten.map(extractFields))
    case nl: SqlNodeList =>
      foldMaps(nl.map(extractFields))
    case j: SqlJoin =>
      if (j.getLeft.isInstanceOf[SqlJoin]) {
        foldMaps(Seq(
          extractFields(j.getCondition),
          extractFields(j.getLeft)
        ))
      } else
        extractFields(j.getCondition)
    case c: SqlCall =>
      foldMaps(Option(c.getOperandList).toSeq.flatten.map(extractFields))
    case i: SqlIdentifier =>
      if (i.names.size() == 2) TreeMap((i.names.get(1) -> Set(i.names.get(0))))
      else if (i.names.size() == 1) TreeMap(i.names.head -> Set("?"))
      else TreeMap.empty
    case _ => TreeMap.empty
  }

  private def reverseFieldsMap(fieldsMap: TreeMap[String, Set[String]]): TreeMap[String, Set[String]] = {
    val seq = for {
      (field, tables) <- fieldsMap.toSeq
      table <- tables
    } yield (table, field)

    val seq2 = seq.groupBy(_._1).map(pair => (pair._1, pair._2.map(_._2).toSet)).toSeq
    TreeMap.apply(seq2: _*)
  }

  private def processJoinFields(join: SqlJoin, name: String, fieldsMap: TreeMap[String, Set[String]]): TreeMap[String, Set[String]] = {
    def extractName(node: SqlNode): String = node match {
      case c: SqlCall =>
        extractName(c.getOperandList.last)
      case i: SqlIdentifier =>
        i.names.last
      case _ => throw new RuntimeException(s"cannot extract table name from $node")
    }

    def processNames(prefix: String, names: Seq[String]): Seq[String] = names.map { s =>
      val arr = s.split("__")
      if (arr.length < 2) s"${prefix}__$s"
      else arr.takeRight(2).mkString("__")
    }

    val left = extractName(join.getLeft)
    val right = extractName(join.getRight)

    val set1 = processNames(left, fieldsMap.get(left).toSeq.flatten)
    val set2 = processNames(right, fieldsMap.get(right).toSeq.flatten)
    val set = set1 ++ set2

    fieldsMap + (name -> set.toSet)
  }

  // 3. Then split query with joins to own queries with only one join
  // should be only one select, i.e., no subqueries;
  // should be no CTEs

  // --------------------------------------------------------------------------

  private def makeSelect(name: String, fieldsMap: TreeMap[String, Set[String]], j: SqlJoin): SqlSelect = {
    val leftIsJoin = j.getLeft.isInstanceOf[SqlIdentifier] && j.getLeft.asInstanceOf[SqlIdentifier].names.head.startsWith("jt_")
    val right = j.getRight.asInstanceOf[SqlCall].getOperandList.last.asInstanceOf[SqlIdentifier].names.last

    def rewriteJoinConds(node: SqlNode): SqlNode = node match {
      case jj: SqlJoin =>
        rewriteJoinConds(jj.getCondition)
        jj
      case i: SqlIdentifier =>
        val names = i.names.toSeq
        if (names.size == 2) {
          val Seq(table, field) = names
          if (table != right && leftIsJoin) i.setNames(List(s"${table}__$field").asJava, List(SqlParserPos.ZERO).asJava)
        }
        i
      case c: SqlCall =>
        c.getOperandList.foreach(rewriteJoinConds)
        c
      case _ => node
    }

    val newSelectList = fieldsMap(name).toSeq.map { s =>
      val Array(table, field) = s.split("__")

      if (table != right && leftIsJoin)
        new SqlIdentifier(List(s).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode]
      else
        new SqlBasicCall(
          new SqlAsOperator,
          Array(new SqlIdentifier(List(table, field).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode], new SqlIdentifier(List(s).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode]),
          SqlParserPos.ZERO)

    }.asJava

    val sqlNodeList = new SqlNodeList(newSelectList, SqlParserPos.ZERO)

    val select = new SqlSelect(SqlParserPos.ZERO, null, sqlNodeList, rewriteJoinConds(j),
      null, null, null, null, null, null, null, null, null)

    select
  }

  def extractJoins2(node: SqlNode, fieldsMap: TreeMap[String, Set[String]], parent: SqlNode = null): (TreeMap[String, SqlNode], TreeMap[String, Set[String]]) = node match {
    case j: SqlJoin =>
      val left = j.getLeft
      if (left.isInstanceOf[SqlJoin]) {
        val (lefts, fm) = extractJoins2(left, fieldsMap, j)
        val name = s"jt_${lefts.size - 1}"

        val newTable = new SqlIdentifier(Seq(name).asJava, SqlParserPos.ZERO)
        j.setLeft(newTable)

        val newFieldsMap = processJoinFields(j, s"jt_${lefts.size}", fm)

        if (parent != null && parent.isInstanceOf[SqlCall]) {
          val bc = parent.asInstanceOf[SqlCall]
          val idx = bc.getOperandList.indexOf(j)
          if (idx > 0) {
            bc.setOperand(idx, new SqlIdentifier(Seq(s"jt_${lefts.size}").asJava, SqlParserPos.ZERO))
          }
        }

        val select = makeSelect(s"jt_${lefts.size}", newFieldsMap, j)
        (lefts.insert(s"jt_${lefts.size}", select), newFieldsMap)
      } else {
        val newFieldsMap = processJoinFields(j, "jt_0", fieldsMap)
        val select = makeSelect("jt_0", newFieldsMap, j)
        (TreeMap(("jt_0", select)), newFieldsMap)
      }
    case c: SqlCall =>
      val joins = Option(c.getOperandList).toIndexedSeq.flatMap(_.toIndexedSeq).filter(_ != null).flatMap { p =>
        val (tree, nfm) = extractJoins2(p, fieldsMap, c)
        tree.map { case (str, node) =>
          str -> (node, nfm)
        }
      }

      val tree = joins.map { case (str, (node, _)) =>
        str -> node
      }

      val nfm = foldMaps(joins.map(_._2._2))

      (TreeMap(tree: _*), nfm)
    case _ =>
      (TreeMap.empty, fieldsMap)
  }

  def extractJoins(alias: String, node: SqlNode): TreeMap[String, SqlNode] = {
    val toExpand = node.clone(SqlParserPos.ZERO)
    val fieldsMap = extractFields(toExpand)
    val revFieldsMap = reverseFieldsMap(fieldsMap)
    val (tree, newFieldsMap) = extractJoins2(toExpand, revFieldsMap)

    if (tree.isEmpty) TreeMap(alias -> node)
    else {
      val select = toExpand.asInstanceOf[SqlSelect]
      val (lastKey, _) = tree.last
      select.setFrom(new SqlIdentifier(Seq(lastKey).asJava, SqlParserPos.ZERO))

      val fieldsSet = newFieldsMap(lastKey)

      def modField(node: SqlNode, parent: SqlNode, lvl: Int = 0): Unit = node match {
        case i: SqlIdentifier if lvl == 0 =>
          if (i.names.size() == 2 && fieldsSet.contains(i.names.mkString("__"))) {
            val newField = new SqlBasicCall(
              new SqlAsOperator,
              Array(new SqlIdentifier(Seq(i.names.mkString("__")).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode], new SqlIdentifier(Seq(i.names(1)).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode]),
              SqlParserPos.ZERO).asInstanceOf[SqlNode]

            val idx = parent.asInstanceOf[SqlNodeList].indexOf(i)
            parent.asInstanceOf[SqlNodeList].set(idx, newField)
          } else ()
        case i: SqlIdentifier =>
          if (i.names.size() == 2 && fieldsSet.contains(i.names.mkString("__"))) {
            val id = new SqlIdentifier(Seq(i.names.mkString("__")).asJava, SqlParserPos.ZERO).asInstanceOf[SqlNode]
            if (parent.isInstanceOf[SqlCall]) {
              val idx = parent.asInstanceOf[SqlCall].getOperandList.indexOf(i)
              parent.asInstanceOf[SqlCall].setOperand(idx, id)
            } else if (parent.isInstanceOf[SqlNodeList]) {
              val idx = parent.asInstanceOf[SqlNodeList].indexOf(i)
              parent.asInstanceOf[SqlNodeList].set(idx, id)
            }
          }
        case c: SqlCall =>
          c.getOperandList.foreach(modField(_, c,  lvl + 1))
        case nl: SqlNodeList =>
          nl.iterator().foreach(modField(_, nl, lvl + 1))
        case _ => ()
      }

      val sl = select.getSelectList
      sl.iterator().foreach(modField(_, sl))

      val wh = select.getWhere
      modField(wh.asInstanceOf[SqlCall], null, 0)

      val result = tree + (alias -> select)
      result
    }
  }


  // --------------------------------------------------------------------------


  // 4. Then - extract window functions
  def extractWindowFuncs(node: SqlNode, parent: SqlNode = null): TreeMap[String, SqlNode] = node match {
    case _ =>
      TreeMap.empty
  }

  /*
  def processAllSql(node: SqlNode): TreeMap[String, SqlNode] = {
    val ctes = extractCTEs(node)
    val subq = ctes.flatMap { case (str, node) =>
      extractSubqueries(node)
    }
    val joins = subq.flatMap { case (_, node) =>

    }
  }

   */

  val sql =
    """
      |select t.id, sum(t.some_value) from (
      |  select
      |    a.id,
      |    b.some_value,
      |    row_number() over (partition by a.id order by b.creation_date desc) as rn
      |    from schema.table1 as a
      |    left join schema.table2 as b on a.id = b.id
      |) as t
      |where rn = 1
      |group by t.id
      |""".stripMargin

  val sql2 =
    """
      |select
      |    a.id,
      |    b.some_value,
      |    row_number() over (partition by a.id order by b.creation_date desc) as rn
      |    from schema.table1 as a
      |    left join schema.table2 as b on a.id = b.id
      |    join schema.table3 as c on c.col = b.col2 and c.col_2 = a.col_2
      |    left join schema.table4 as d on d.col3 = c.col3
      |    left join (
      |      select * from schema.table5
      |    ) as e on e.col4 = d.col4
      |  where c.col3 in (1, 2, 3)
      |""".stripMargin

  val sql3 =
    """
      |select * from (
      |  select * from (
      |    select * from (
      |      select * from table1
      |    ) as t3
      |  ) as t2
      |) as t1
      |""".stripMargin

  val sql4 =
    """
      |with a as (
      |  select * from table1
      |), b as (
      |  select * from table2
      |)
      |select * from a
      |join b on a.id = b.id
      |""".stripMargin

  val sql5 =
    """
      |select
      |  a.id,
      |  a.client_name,
      |  a.client_desc,
      |  b.payment_amount,
      |  b.last_date
      |from table1 as a
      |join table2 as b on a.id = b.client_id
      |where b.last_date > '2022-01-01'
      |""".stripMargin

  val sql6 =
    """
      |select
      |    a.id,
      |    b.some_value,
      |    row_number() over (partition by a.id order by b.creation_date desc) as rn
      |    from schema.table1 as a
      |    left join schema.table2 as b on a.id = b.id
      |    join schema.table3 as c on c.col = b.col2
      |    left join schema.table4 as d on d.col3 = c.col3
      |  where c.col3 in (1, 2, 3)
      |""".stripMargin

  val node = parser.parseQuery(sql)
  val node2 = parser.parseQuery(sql2)
  val node3 = parser.parseQuery(sql3)
  val node4 = parser.parseQuery(sql4)
  val node5 = parser.parseQuery(sql5)
  val node6 = parser.parseQuery(sql6)

  // CTES
  //println(node4)
  //val exctes = extractCTEs(node4)
  //println(exctes)
  //val exctes2 = extractCTEs(node2)
  //println(exctes2)

  //val ex5 = extractJoins(node5)
  //println(ex5)

  val ef6 = extractFields(node6)
  println(ef6)

  //println(node)

  //val ind = process(node)

  //println("ind: " + ind)

  //val ind2 = process(node2)

  //println("NODE 2" + ind2)

  //val ex = extractSubqueries(node)
  val ex2 = extractSubqueries(node2)

  println(ex2)

  val js = ex2.flatMap { p =>
    /*val fm = extractFields(p._2)
    val revFm = reverseFieldsMap(fm)
    val (j, _) = extractJoins2(p._2, revFm)
    j.insert(p._1, p._2)*/

    val j = extractJoins(p._1, p._2)

    j
  }

  println(js)

  val ex3 = extractSubqueries(node3)

  println(ex3)
}
