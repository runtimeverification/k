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
class Att private (val att: Map[(Att.Key, String), Any]) extends AttributesToString with Serializable {

  override lazy val hashCode: Int = att.hashCode()
  override def equals(that: Any): Boolean = that match {
    case a: Att => a.att == att
    case _ => false
  }

  lazy val unrecognizedAtts: Set[Att.Key] =
    att.filter((p) => !(p._2.isInstanceOf[Att.GroupMarker] || Att.getWhitelistedOptional(p._1._1.toString).isPresent))
      .map((p) => p._1._1)
      .toSet

  def getMacro: Option[Att.Key] = {
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
    None
  }

  def contains(cls: Class[_]): Boolean = att.contains((Att.getWhitelisted(cls.getName), cls.getName))
  def contains(key: Att.Key): Boolean = att.contains((key, Att.stringClassName))
  def contains(key: Att.Key, cls: Class[_]): Boolean = att.contains((key, cls.getName))

  def get[T](key: Class[T]): T = getOption(key).get
  def get(key: Att.Key): String = getOption(key).get
  def get[T](key: Att.Key, cls: Class[T]): T = getOption(key, cls).get
  def getOption(key: Att.Key): Option[String] = att.get((key, Att.stringClassName)).asInstanceOf[Option[String]]
  def getOption[T](key: Class[T]): Option[T] = att.get((Att.getWhitelisted(key.getName), key.getName)).asInstanceOf[Option[T]]
  def getOption[T](key: Att.Key, cls: Class[T]): Option[T] = att.get((key, cls.getName)).asInstanceOf[Option[T]]
  def getOptional(key: Att.Key): Optional[String] = optionToOptional(getOption(key))
  def getOptional[T](key: Class[T]): Optional[T] = optionToOptional(getOption(key))
  def getOptional[T](key: Att.Key, cls: Class[T]): Optional[T] = optionToOptional(getOption(key, cls))

  private def optionToOptional[T](option: Option[T]): Optional[T] =
    option match {case None => Optional.empty(); case Some(x) => Optional.of(x);}

  def add(key: Att.Key): Att = add(key, "")
  def add(key: Att.Key, value: String): Att = add(key, Att.stringClassName, value)
  def add(key: Att.Key, value: Int): Att = add(key, Att.intClassName, value)
  def add[T <: AttValue](key: Class[T], value: T): Att = add(Att.getWhitelisted(key.getName), key.getName, value)
  def add[T <: AttValue](key: Att.Key, cls: Class[T], value: T): Att = add(key, cls.getName, value)
  private def add[T <: AttValue](key: Att.Key, clsStr: String, value: T): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: Att.Key, clsStr: String, value: String): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: Att.Key, clsStr: String, value: Int): Att = Att(att + ((key, clsStr) -> value))
  def addAll(thatAtt: Att): Att = Att(att ++ thatAtt.att)
  def addGroup(key: String): Att = add(Att.Key(key), Att.groupMarkerClassName, Att.GroupMarker())
  def remove(key: Att.Key): Att = remove(key, Att.stringClassName)
  def remove(key: Class[_]): Att = remove(Att.getWhitelisted(key.getName), key.getName)
  def remove(key: Att.Key, cls: Class[_]): Att = remove(key, cls.getName)
  private def remove(key: Att.Key, clsStr: String): Att = Att(att - ((key, clsStr)))

  /**
   * NOTE: Do not use this function except during parsing!
   *
   * This is only used so that we can delay error checking until after parsing finishes, allowing us to report multiple
   * errors rather than exiting immediately.
   */
  def unsafeAddAttributeToBeErrorCheckedElsewhere(key: String, value: String): Att = add(Att.Key(key), value)
}


object Att {
  // The Key constructor is private, enforcing that attributes can only be defined within this object
  case class Key private[Att](private[Att] val key: String) extends Serializable {
    override def toString: String = this.key
    // goodKey.copy(key="bad-att") would be the same as constructing Att.Key("bad-att"),
    // so manually declare to make private
    private[Key] def copy(): Unit = ()
  }
  object Key {
    private[Att] def apply(key: String): Key = new Key(key)
  }

  val empty: Att = Att(Map.empty)

  // Note: Any field Att.UPPER_CASE_NAME of Att.Key type is automatically added to the
  // whitelist of attribute keys (through reflection).
  final val ALIAS = Key("alias")
  final val ALIAS_REC = Key("alias-rec")
  final val ALL_PATH = Key("all-path")
  final val ANONYMOUS = Key("anonymous")
  final val ANYWHERE = Key("anywhere")
  final val APPLY_PRIORITY = Key("applyPriority")
  final val ASSOC = Key("assoc")
  final val AVOID = Key("avoid")
  final val BAG = Key("bag")
  final val BINDER = Key("binder")
  final val BRACKET = Key("bracket")
  final val BRACKET_LABEL = Key("bracketLabel")
  final val CELL = Key("cell")
  final val CELL_COLLECTION = Key("cellCollection")
  final val CELL_FRAGMENT = Key("cellFragment")
  final val CELL_NAME = Key("cellName")
  final val CELL_OPT_ABSENT = Key("cellOptAbsent")
  final val CELL_SORT = Key("cellSort")
  final val CHOICE = Key("choice")
  final val COLOR = Key("color")
  final val COLORS = Key("colors")
  final val COMM = Key("comm")
  final val CONCAT = Key("concat")
  final val CONCRETE = Key("concrete")
  final val CONSTRUCTOR = Key("constructor")
  final val CONTENT_START_COLUMN = Key("contentStartColumn")
  final val CONTENT_START_LINE = Key("contentStartLine")
  final val CONTEXT = Key("context")
  final val COOL = Key("cool")
  final val COOL_LIKE = Key("cool-like")
  final val DENORMAL = Key("denormal")
  final val DIGEST = Key("digest")
  final val DUMMY_CELL = Key("dummy_cell")
  final val ELEMENT = Key("element")
  final val EXIT = Key("exit")
  final val FILTER_ELEMENT = Key("filterElement")
  final val FORMAT = Key("format")
  final val FRESH = Key("fresh")
  final val FRESH_GENERATOR = Key("freshGenerator")
  final val FUNCTION = Key("function")
  final val FUNCTIONAL = Key("functional")
  final val GENERATED_BY_LIST_SUBSORTING = Key("generatedByListSubsorting")
  final val GROUP = Key("group")
  final val HAS_DOMAIN_VALUES = Key("hasDomainValues")
  final val HEAT = Key("heat")
  final val HYBRID = Key("hybrid")
  final val HOOK = Key("hook")
  final val IDEM = Key("idem")
  final val IMPURE = Key("impure")
  final val INITIAL = Key("initial")
  final val INITIALIZER = Key("initializer")
  final val INJECTIVE = Key("injective")
  final val INTERNAL = Key("internal")
  final val KAST = Key("kast")
  final val KLABEL = Key("klabel")
  final val KORE = Key("kore")
  final val LABEL = Key("label")
  final val LATEX = Key("latex")
  final val LEFT = Key("left")
  final val LEMMA = Key("lemma")
  final val LOCATION = Key("org.kframework.attributes.Location")
  final val LOCATIONS = Key("locations")
  final val LOOKUP = Key("lookup")
  final val MACRO = Key("macro")
  final val MACRO_REC = Key("macro-rec")
  final val MAINCELL = Key("maincell")
  final val MEMO = Key("memo")
  final val ML_BINDER = Key("mlBinder")
  final val ML_OP = Key("mlOp")
  final val MULTIPLICITY = Key("multiplicity")
  final val NAT = Key("nat")
  final val NO_THREAD = Key("noThread")
  final val NON_ASSOC = Key("non-assoc")
  final val NON_EXECUTABLE = Key("non-executable")
  final val NOT_INJECTION = Key("notInjection")
  final val NOT_LR1 = Key("not-lr1")
  final val ONE_PATH = Key("one-path")
  final val ORIGINAL_NAME = Key("originalName")
  final val ORIGINAL_PRD = Key("originalPrd")
  final val OWISE = Key("owise")
  final val PARSER = Key("parser")
  final val PATTERN = Key("pattern")
  final val PATTERN_FOLDING = Key("pattern-unfolding")
  final val PREC = Key("prec")
  final val PREDICATE = Key("predicate")
  final val PREFER = Key("prefer")
  final val PRETTY_PRINT_WITH_SORT_ANNOTATION = Key("prettyPrintWithSortAnnotation")
  final val PRIORITIES = Key("priorities")
  final val PRIORITY = Key("priority")
  final val PRIVATE = Key("private")
  final val PRODUCTION = Key("org.kframework.definition.Production")
  final val PRODUCTION_ID = Key("productionId")
  final val PROJECTION = Key("projection")
  final val PUBLIC = Key("public")
  final val RECORD_PRD = Key("recordPrd")
  final val RECORD_PRD_ZERO = Key("recordPrd-zero")
  final val RECORD_PRD_ONE = Key("recordPrd-one")
  final val RECORD_PRD_MAIN = Key("recordPrd-main")
  final val RECORD_PRD_EMPTY = Key("recordPrd-empty")
  final val RECORD_PRD_SUBSORT = Key("recordPrd-subsort")
  final val RECORD_PRD_REPEAT = Key("recordPrd-repeat")
  final val RECORD_PRD_ITEM = Key("recordPrd-item")
  final val REFRESHED = Key("refreshed")
  final val REGEX = Key("regex")
  final val REJECT = Key("reject")
  final val REMOVE = Key("remove")
  final val RESULT = Key("result")
  final val RETURNS_UNIT = Key("returnsUnit")
  final val RIGHT = Key("right")
  final val SEQSTRICT = Key("seqstrict")
  final val SIMPLIFICATION = Key("simplification")
  final val SMTLIB = Key("smtlib")
  final val SMT_HOOK = Key("smt-hook")
  final val SMT_LEMMA = Key("smt-lemma")
  final val SMT_PRELUDE = Key("smt-prelude")
  final val SORT = Key("org.kframework.kore.Sort")
  final val SORT_PARAMS = Key("sortParams")
  final val SOURCE = Key("org.kframework.attributes.Source")
  final val STREAM = Key("stream")
  final val STRICT = Key("strict")
  final val SYMBOL = Key("symbol")
  final val SYMBOLIC = Key("symbolic")
  final val SYNTAX_MODULE = Key("syntaxModule")
  final val TAG = Key("tag")
  final val TEMPORARY_CELL_SORT_DECL = Key("temporary-cell-sort-decl")
  final val TERMINALS = Key("terminals")
  final val TOKEN = Key("token")
  final val TOPCELL = Key("topcell")
  final val TOTAL = Key("total")
  final val TRANSITION = Key("transition")
  final val TRUSTED = Key("trusted")
  final val TYPE = Key("type")
  final val UNBLOCK = Key("unblock")
  final val UNBOUND_VARIABLES = Key("unboundVariables")
  final val UNIT = Key("unit")
  final val UNIQUE_ID = Key("UNIQUE_ID")
  final val UNPARSE_AVOID = Key("unparseAvoid")
  final val UNUSED = Key("unused")
  final val USER_LIST = Key("userList")
  final val USER_LIST_TERMINATOR = Key("userListTerminator")
  final val WITH_CONFIG = Key("withConfig")
  final val WRAP_ELEMENT = Key("wrapElement")

  private val stringClassName = classOf[String].getName
  private val intClassName = classOf[java.lang.Integer].getName

  // Marker for group(...) attributes
  case class GroupMarker() extends AttValue
  private val groupMarkerClassName = classOf[GroupMarker].getName

  // All String fields with UPPER_CASE naming are considered part of the whitelist
  private val whitelist: Set[Key] =
    Att.getClass.getDeclaredFields
      .filter(f => f.getType.equals(classOf[Key]) && f.getName.matches("[A-Z]+(_[A-Z]+)*"))
      .map(f => f.get(this).asInstanceOf[Key])
      .toSet

  // Get the corresponding Att.Key if key is a whitelisted attribute
  def getWhitelistedOptional(key: String): Optional[Key] =
    if (whitelist.contains(Att.Key(key))) {
      Optional.of(Att.Key(key))
    } else {
      Optional.empty()
    }
  def getWhitelisted(key: String): Key =
    getWhitelistedOptional(key).orElseThrow(() =>
       new AssertionError(
        "Called getWhitelisted(" + key + "), but " + key + " was not found in the attribute whitelist.\n" +
          "To add a new attribute key, create a field `final val MY_ATT = Key(\"my-att\")` in the Att object."))

  def from(thatAtt: java.util.Map[Key, String]): Att =
    Att(immutable(thatAtt).map { case (k, v) => ((k, Att.stringClassName), v) }.toMap)

  private def apply(thatAtt: Map[(Key, String), Any]) = {
    new Att(thatAtt)
  }

  def mergeAttributes(p: Set[Att]): Att = {
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
    att filter { case ((Att.PRODUCTION_ID, _), _) => false; case _ => true } map
      { case ((key, `stringClassName`), "") => key.toString
        case ((key, _), value) => key.toString + "(" + value + ")" } toList
  }
}
