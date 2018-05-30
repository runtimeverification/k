package org.kframework.attributes

import java.util.Optional

import org.kframework.Collections._

case class Att(att: Map[(String, Class[_]), Any]) extends AttributesToString {

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Att.this)

  def contains(cls: Class[_]): Boolean = att.contains((cls.getName, cls))
  def contains(key: String): Boolean = att.contains((key, classOf[String]))
  def contains(key: String, cls: Class[_]): Boolean = att.contains((key, cls))

  def get[T](key: Class[T]): T = getOption(key).get
  def get(key: String): String = getOption(key).get
  def get[T](key: String, cls: Class[T]): T = getOption(key, cls).get
  def getOption(key: String): Option[String] = att.get((key, classOf[String])).asInstanceOf[Option[String]]
  def getOption[T](key: Class[T]): Option[T] = att.get((key.getName, key)).asInstanceOf[Option[T]]
  def getOption[T](key: String, cls: Class[T]): Option[T] = att.get((key, cls)).asInstanceOf[Option[T]]
  def getOptional(key: String): Optional[String] = optionToOptional(getOption(key))
  def getOptional[T](key: Class[T]): Optional[T] = optionToOptional(getOption(key))
  def getOptional[T](key: String, cls: Class[T]): Optional[T] = optionToOptional(getOption(key, cls))

  private def optionToOptional[T](option: Option[T]): Optional[T] = option match { case None => Optional.empty(); case Some(x) => Optional.of(x); }

  def add(key: String): Att = add(key, "")
  def add(key: String, value: String): Att = add(key, classOf[String], value)
  def add[T](key: String, cls: Class[T], value: T): Att = Att(att + ((key, cls) -> value))
  def add[T](key: Class[T], value: T): Att = add(key.getName, key, value)
  def addAll(thatAtt: Att) = Att(att ++ thatAtt.att)
  def addAll(thatAtt: java.util.Map[String, String]): Att = Att(immutable(thatAtt).map { case (k, v) => ((k, classOf[String]), v)}.toMap)

  def remove(key: String): Att = remove(key, classOf[String])
  def remove(key: Class[_]): Att = remove(key.getName, key)
  def remove(key: String, cls: Class[_]): Att = Att(att - ((key, cls)))
}

object Att {

  val empty: Att = Att(Map.empty)

  /**
   * attribute marking the top rule label
   */
  val topRule = "topRule"
  val userList = "userList"
  val generatedByListSubsorting = "generatedByListSubsorting"
  val generatedBy = "generatedBy"
  val ClassFromUp = "classType"
  val Location = "location"
  val Function = "function"
  val transition = "transition"
  val heat = "heat"
  val cool = "cool"
  val stuck = "#STUCK"
  val refers_THIS_CONFIGURATION = "refers_THIS_CONFIGURATION"
  val refers_RESTORE_CONFIGURATION = "refers_RESTORE_CONFIGURATION"
  val assoc = "assoc"
  val comm = "comm"
  val unit = "unit"
  val bag = "bag"
  val syntaxModule = "syntaxModule"
  val variable = "variable"
}

trait AttributesToString {
  self: Att =>

  override def toString =
    "[" +
      toStrings.sorted.mkString(" ") +
    "]"

  def postfixString = {
    if (toStrings.isEmpty) "" else " " + toString()
  }

  lazy val toStrings: List[String] =
    att filter { case (("productionId", _), _) => false; case _ => true } map
      { case ((key, _), value) => key + "(" + value + ")" } toList
}
