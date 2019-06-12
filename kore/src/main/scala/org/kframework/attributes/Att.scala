package org.kframework.attributes

import java.util.Optional

import org.kframework.Collections._

/**
 * 2nd value in key is always a class name. For a key of type (s1, s2), value must be of type class.forName(s2).
 */
case class Att(att: Map[(String, String), Any]) extends AttributesToString {

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Att.this)

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
  def add[T](key: Class[T], value: T): Att = add(key.getName, key.getName, value)
  def add[T](key: String, cls: Class[T], value: T): Att = add(key, cls.getName, value)
  private def add[T](key: String, clsStr: String, value: T): Att = Att(att + ((key, clsStr) -> value))
  def addAll(thatAtt: Att) = Att(att ++ thatAtt.att)

  def remove(key: String): Att = remove(key, Att.stringClassName)
  def remove(key: Class[_]): Att = remove(key.getName, key.getName)
  def remove(key: String, cls: Class[_]): Att = remove(key, cls.getName)
  private def remove(key: String, clsStr: String): Att = Att(att - ((key, clsStr)))
}

object Att {

  val empty: Att = Att(Map.empty)

  /**
   * attribute marking the top rule label
   */
  val topRule = "topRule"
  val specification = "specification"
  val userList = "userList"
  val generatedByListSubsorting = "generatedByListSubsorting"
  val generatedBy = "generatedBy"
  val ClassFromUp = "classType"
  val Location = "location"
  val Function = "function"
  val transition = "transition"
  val heat = "heat"
  val cool = "cool"
  val refers_THIS_CONFIGURATION = "refers_THIS_CONFIGURATION"
  val refers_RESTORE_CONFIGURATION = "refers_RESTORE_CONFIGURATION"
  val assoc = "assoc"
  val comm = "comm"
  val unit = "unit"
  val bag = "bag"
  val syntaxModule = "syntaxModule"
  val variable = "variable"

  private val stringClassName = classOf[String].getName

  def from(thatAtt: java.util.Map[String, String]): Att =
    Att(immutable(thatAtt).map { case (k, v) => ((k, Att.stringClassName), v) }.toMap)
}

trait AttributesToString {
  self: Att =>

  override def toString: String = "[" + toStrings.sorted.mkString(" ") + "]"

  def postfixString: String = {
    if (toStrings.isEmpty) "" else " " + toString()
  }

  lazy val toStrings: List[String] =
    att filter { case (("productionId", _), _) => false; case _ => true } map
      { case ((key, _), value) => key + "(" + value + ")" } toList
}
