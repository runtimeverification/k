package org.kframework.koreimplementation

//case class Att(att: Set[K] = Set()) extends Collection[K] with Indexed[String, KList] with AttributesToString {
//  type This = Att
//
//  def contains(label: String): Boolean = (att find {
//    case KApply(KLabel(`label`), _, _) => true
//    case _ => false
//  }) != None
//
//  def get(label: String): Option[KList] = att collect {
//    case KApply(KLabel(`label`), l, _) => l
//  } headOption
//
//  def getString(label: String): Option[String] = att collect {
//    case KApply(KLabel(`label`), KList(KToken(_, l, _)), _) => l
//  } headOption
//
//  def getOptionalString(label: String): java.util.Optional[String] =
//    getString(label) match {
//      case Some(s) => java.util.Optional.of(s);
//      case None => java.util.Optional.empty[String]()
//    }
//
//  def addAll(that: Att) = this ++ that
//
//  def foreach(f: K => Unit): Unit = att foreach f
//
//  def iterable: Iterable[K] = att
//
//  def newBuilder: Builder[K, Att] = new SetBuilder[K, Set[K]](Set()) mapResult { new Att(_) }
//
//  def +(k: K): Att = new Att(att + k)
//  def +(k: String): Att = add(KApply(KLabel(k), KList()))
//  def +(kv: (String, String)): Att = add(KApply(KLabel(kv._1), KList(KToken(Sorts.KString, kv._2))))
//
//  def ++(that: Att) = new Att(att ++ that.att)
//
//  // nice methods for Java
//  def add(k: K): Att = this + k
//  def add(k: String): Att = this + k
//  def add(key: String, value: String): Att = this + (key -> value)
//
//  def matchAll(k: K)(implicit disj: Theory): Or = {
//    ???
//  }
//
//  override def equals(that: Any) = that.isInstanceOf[Att]
//}
//
//object Att {
//  def apply(ks: K*) = new Att(ks.toSet)
//
//  val classFromUp = "classType"
//}
//
////case class Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) {
////
////  // TODO: Radu: Add offset when the parser knows how to compute it.
////}
//
//object Location {
//  import KORE._
//
//  def apply(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = {
//    'location('startLine(Sorts.Int(startLine.toString)), 'startColumn(Sorts.Int(startColumn.toString)),
//      'endLine(Sorts.Int(endLine.toString)), 'endColumn(Sorts.Int(endColumn.toString)))
//  }
//}
//
//trait AttributesToString {
//  self: Att =>
//
//  override def toString() =
//    "[" +
//      (this.filteredAtt map {
//        case KApply(KLabel(keyName), KList(KToken(_, value, _)), _) => keyName + "(" + value + ")"
//        case x => x.toString
//      }).toList.sorted.mkString(" ") +
//      "]"
//
//  def postfixString = {
//    if (filteredAtt.isEmpty) "" else (" " + toString())
//  }
//
//  lazy val filteredAtt: Set[K] = att filter { case KApply(KLabel("productionID"), _, _) => false; case _ => true } // TODO: remove along with KIL to KORE to KIL convertors
//}
