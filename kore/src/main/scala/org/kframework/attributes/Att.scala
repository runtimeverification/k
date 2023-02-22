// Copyright (c) K Team. All Rights Reserved.
package org.kframework.attributes

import java.util.Optional

import org.kframework.Collections._
import scala.collection.Set

/**
 * Marker class for objects that can be stored as the value of an attribute.
 *
 * So far this trait implements no methods, but in the future it may
 * include some methods relating to serialization/deserialization that
 * all inheritors must implement. It may depend on what serialization library
 * we choose to use going forward.
 */
trait AttValue

/**
 * 2nd value in key is always a class name. For a key of type (s1, s2), value must be of type class.forName(s2).
 */
class Att private (val att: Map[(String, String), Any]) extends AttributesToString with Serializable {

  override lazy val hashCode: Int = att.hashCode()
  override def equals(that: Any) = that match {
    case a: Att => a.att == att
    case _ => false
  }

  def getMacro: Option[String] = {
    if (contains(Att.MACRO)){
      return Some(Att.MACRO)
    }
    if (contains(Att.MACRO_REC)) {
      return Some(Att.MACRO_REC)
    }
    if (contains(Att.ALIAS)) {
      return Some(Att.ALIAS)
    }
    if (contains(Att.ALIAS_REC)) {
      return Some(Att.ALIAS_REC)
    }
    return None;
  }

  def contains(cls: Class[_]): Boolean = att.contains((cls.getName, cls.getName))
  def contains(key: String): Boolean = att.contains((key, Att.stringClassName))
  def contains(key: String, cls: Class[_]): Boolean = att.contains((key, cls.getName))

  def get[T](key: Class[T]): T = getOption(key).get
  def get(key: String): String = getOption(key).get
  def get[T](key: String, cls: Class[T]): T = getOption(key, cls).get
  def getOption(key: String): Option[String] = att.get((key, Att.stringClassName)).asInstanceOf[Option[String]]
  def getOption[T](key: Class[T]): Option[T] = att.get((key.getName, key.getName)).asInstanceOf[Option[T]]
  def getOption[T](key: String, cls: Class[T]): Option[T] = att.get((key, cls.getName)).asInstanceOf[Option[T]]
  def getOptional(key: String): Optional[String] = optionToOptional(getOption(key))
  def getOptional[T](key: Class[T]): Optional[T] = optionToOptional(getOption(key))
  def getOptional[T](key: String, cls: Class[T]): Optional[T] = optionToOptional(getOption(key, cls))

  private def optionToOptional[T](option: Option[T]): Optional[T] =
    option match {case None => Optional.empty(); case Some(x) => Optional.of(x);}

  def add(key: String): Att = add(key, "")
  def add(key: String, value: String): Att = add(key, Att.stringClassName, value)
  def add(key: String, value: Int): Att = add(key, Att.intClassName, value)
  def add[T <: AttValue](key: Class[T], value: T): Att = add(key.getName, key.getName, value)
  def add[T <: AttValue](key: String, cls: Class[T], value: T): Att = add(key, cls.getName, value)
  private def add[T <: AttValue](key: String, clsStr: String, value: T): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: String, clsStr: String, value: String): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: String, clsStr: String, value: Int): Att = Att(att + ((key, clsStr) -> value))
  def addAll(thatAtt: Att) = Att(att ++ thatAtt.att)

  def remove(key: String): Att = remove(key, Att.stringClassName)
  def remove(key: Class[_]): Att = remove(key.getName, key.getName)
  def remove(key: String, cls: Class[_]): Att = remove(key, cls.getName)
  private def remove(key: String, clsStr: String): Att = Att(att - ((key, clsStr)))
}

object Att {

  val empty: Att = Att(Map.empty)

  val ALIAS = "alias"
  val ALIAS_REC = "alias-rec"
  val ALL_PATH = "all-path"
  val ANYWHERE = "anywhere"
  val ASSOC = "assoc"
  val BAG = "bag"
  val BITWIDTH = "bitwidth"
  val BRACKET = "bracket"
  val CELL = "cell"
  val CELL_FRAGMENT = "cellFragment"
  val CELL_OPT_ABSENT = "cellOptAbsent"
  val COMM = "comm"
  val CONCRETE = "concrete"
  val COOL = "cool"
  val DIGEST = "digest"
  val EXPONENT = "exponent"
  val FUNCTION = "function"
  val FUNCTIONAL = "functional"
  val GENERATED_BY_LIST_SUBSORTING = "generatedByListSubsorting"
  val HEAT = "heat"
  val HOOK = "hook"
  val IDEM = "idem"
  val IMPURE = "impure"
  val KORE = "kore"
  val LABEL = "label"
  val LEMMA = "lemma"
  val LOCATION = "org.kframework.attributes.Location"
  val MACRO = "macro"
  val MACRO_REC = "macro-rec"
  val MAINCELL = "maincell"
  val MATCHING = "matching"
  val NON_EXECUTABLE = "non-executable"
  val ONE_PATH = "one-path"
  val ORIGINAL_PRD = "originalPrd"
  val OWISE = "owise"
  val PATTERN = "pattern"
  val PATTERN_FOLDING = "pattern-folding"
  val PREDICATE = "predicate"
  val PRIORITY = "priority"
  val PRIVATE = "private"
  val PROJ = "proj"
  val PUBLIC = "public"
  val RECORD_PRD = "recordPrd"
  val REFERS_RESTORE_CONFIGURATION = "refers_RESTORE_CONFIGURATION"
  val REFERS_THIS_CONFIGURATION = "refers_THIS_CONFIGURATION";
  val SEQSTRICT = "seqstrict"
  val SIGNIFICAND = "significand"
  val SIMPLIFICATION = "simplification"
  val SMTLIB = "smtlib"
  val SMT_HOOK = "smt-hook"
  val SMT_LEMMA = "smt-lemma"
  val SMT_PRELUDE = "smt-prelude"
  val SOURCE = "org.kframework.attributes.Source"
  val SPECIFICATION = "specification"
  val STRICT = "strict"
  val SYMBOLIC = "symbolic"
  val SYNTAX_MODULE = "syntaxModule"
  val TAG = "tag"
  val TOKEN = "token"
  val TOP_RULE = "topRule"
  val TOTAL = "total"
  val TRANSITION = "transition"
  val TRUSTED = "trusted"
  val UNBOUND_VARIABLES = "unboundVariables"
  val UNIT = "unit"
  val UNIQUE_ID = "UNIQUE_ID"
  val USER_LIST = "userList"

  private val stringClassName = classOf[String].getName
  private val intClassName = classOf[java.lang.Integer].getName

  def from(thatAtt: java.util.Map[String, String]): Att =
    Att(immutable(thatAtt).map { case (k, v) => ((k, Att.stringClassName), v) }.toMap)

  private def apply(thatAtt: Map[(String, String), Any]) = {
    new Att(thatAtt)
  }

  def mergeAttributes(p: Set[Att]) = {
    val union = p.flatMap(_.att)
    val attMap = union.groupBy({ case ((name, _), _) => name})
    Att(union.filter { key => attMap(key._1._1).size == 1 }.toMap)
  }

}

trait AttributesToString {
  self: Att =>

  override def toString: String = {
    if (att.isEmpty) {
      ""
    } else {
      "[" + toStrings.sorted.mkString(", ") + "]"
    }
  }

  def postfixString: String = {
    if (toStrings.isEmpty) "" else " " + toString()
  }


  lazy val toStrings: List[String] = {
    val stringClassName = classOf[String].getName
    att filter { case (("productionId", _), _) => false; case _ => true } map
      { case ((key, `stringClassName`), "") => key
        case ((key, _), value) => key + "(" + value + ")" } toList
  }
}
