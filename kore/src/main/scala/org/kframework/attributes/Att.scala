// Copyright (c) K Team. All Rights Reserved.
package org.kframework.attributes

import java.util.Optional
import org.kframework.Collections._

import java.lang.Enum
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
 * Conceptually, attributes are a mapping from String keys to values of any type.
 *
 * However, there are two caveats:
 * - We store the type of the value in the key. That is, a key is a pair (s1, s2) where the corresponding value must
 *   have type class.forName(s2).
 * - We use a wrapper Att.Key(String,KeyType) than a raw String key. This helps to enforce access controls and allows 
 *   for easier IDE navigation to where each attribute is used.
 *
 * New attributes should be added as a Key field Att.MY_NEW_ATT in the object below.
 *
 * To obtain an appropriate Key, use
 * - Att.MY_ATT, if you statically know the key you want
 * - Att.getBuiltInKeyOptional(myAttStr), if checking a user-supplied attribute string. Be sure to report an error
 *   if the lookup fails and --pedantic-attributes is enabled.
 * - Att.getInternalKeyOptional(myAttStr), if expecting an internal key
 * - Att.getUserGroupOptional(myAttStr), if expecting a user-group, enforcing that it is neither a built-in nor internal
 * 
 * In rare circumstances, you may also use Att.unsafeRawKey(myAttStr) if you pinky-promise to check the keys are valid
 * and categorize them elsewhere (e.g. during parsing to allow us to report multiple errors)
 */
class Att private (val att: Map[(Att.Key, String), Any]) extends AttributesToString with Serializable {

  override lazy val hashCode: Int = att.hashCode()
  override def equals(that: Any): Boolean = that match {
    case a: Att => a.att == att
    case _ => false
  }

  // All those raw keys which are not categorized
  val rawKeys: Set[Att.Key] =
    att.map(_._1._1).filter(_.keyType.equals(Att.KeyType.Raw)).toSet

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

  def contains(cls: Class[_]): Boolean = att.contains((Att.getInternalKeyOrAssert(cls.getName), cls.getName))
  def contains(key: Att.Key): Boolean = att.contains((key, Att.stringClassName))
  def contains(key: Att.Key, cls: Class[_]): Boolean = att.contains((key, cls.getName))

  def get[T](key: Class[T]): T = getOption(key).get
  def get(key: Att.Key): String = getOption(key).get
  def get[T](key: Att.Key, cls: Class[T]): T = getOption(key, cls).get
  def getOption(key: Att.Key): Option[String] = att.get((key, Att.stringClassName)).asInstanceOf[Option[String]]
  def getOption[T](key: Class[T]): Option[T] = att.get((Att.getInternalKeyOrAssert(key.getName), key.getName)).asInstanceOf[Option[T]]
  def getOption[T](key: Att.Key, cls: Class[T]): Option[T] = att.get((key, cls.getName)).asInstanceOf[Option[T]]
  def getOptional(key: Att.Key): Optional[String] = optionToOptional(getOption(key))
  def getOptional[T](key: Class[T]): Optional[T] = optionToOptional(getOption(key))
  def getOptional[T](key: Att.Key, cls: Class[T]): Optional[T] = optionToOptional(getOption(key, cls))

  private def optionToOptional[T](option: Option[T]): Optional[T] =
    option match {case None => Optional.empty(); case Some(x) => Optional.of(x);}

  def add(key: Att.Key): Att = add(key, "")
  def add(key: Att.Key, value: String): Att = add(key, Att.stringClassName, value)
  def add(key: Att.Key, value: Int): Att = add(key, Att.intClassName, value)
  def add[T <: AttValue](key: Class[T], value: T): Att = add(Att.getInternalKeyOrAssert(key.getName), key.getName, value)
  def add[T <: AttValue](key: Att.Key, cls: Class[T], value: T): Att = add(key, cls.getName, value)
  private def add[T <: AttValue](key: Att.Key, clsStr: String, value: T): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: Att.Key, clsStr: String, value: String): Att = Att(att + ((key, clsStr) -> value))
  private def add(key: Att.Key, clsStr: String, value: Int): Att = Att(att + ((key, clsStr) -> value))
  def addAll(thatAtt: Att): Att = Att(att ++ thatAtt.att)
  def remove(key: Att.Key): Att = remove(key, Att.stringClassName)
  def remove(key: Class[_]): Att = remove(Att.getInternalKeyOrAssert(key.getName), key.getName)
  def remove(key: Att.Key, cls: Class[_]): Att = remove(key, cls.getName)
  private def remove(key: Att.Key, clsStr: String): Att = Att(att - ((key, clsStr)))
}

object Att {

  sealed trait KeyType
  private object KeyType extends Serializable {
    // Attributes which are built-in and can appear in user source code
    case object BuiltIn extends KeyType;
    // Attributes which are compiler-internal and cannot appear in user source code
    case object Internal extends KeyType;
    // Attributes which represent user-defined groups via group(_)
    case object UserGroup extends KeyType;
    // Attributes which may be a BuiltIn/Internal/UserGroup, but have not been checked or categorized
    // This is mainly used during parsing to delay error checking, allowing us to report multiple errors
    case object Raw extends KeyType;
  }

  /* The Key class can only be constructed within Att. To enforce this, we must
   * - Make the constructor private
   * - Manually declare apply() and make it private, lest a public one is generated
   * - Manually declare copy() and make it private, preventing constructions like Att.GOOD_KEY.copy(key="bad-att")
   */
  case class Key private[Att](key: String, keyType: KeyType) extends Serializable {
    override def toString: String = key
    private[Key] def copy(): Unit = ()
  }
  object Key {
    private[Att] def apply(key: String, keyType: KeyType): Key = new Key(key, keyType)
  }

  /*
   * WARNING: Only use this in exceptional circumstances (e.g. during parsing)!
   */
  def unsafeRawKey(key: String): Att.Key =
    Att.Key(key, KeyType.Raw)

  val empty: Att = Att(Map.empty)

  /*
   * Built-in attribute keys which can appear in user source code
   */
  final val ALIAS = Key("alias", KeyType.BuiltIn)
  final val ALIAS_REC = Key("alias-rec", KeyType.BuiltIn)
  final val ALL_PATH = Key("all-path", KeyType.BuiltIn)
  final val ANYWHERE = Key("anywhere", KeyType.BuiltIn)
  final val APPLY_PRIORITY = Key("applyPriority", KeyType.BuiltIn)
  final val ASSOC = Key("assoc", KeyType.BuiltIn)
  final val AVOID = Key("avoid", KeyType.BuiltIn)
  final val BAG = Key("bag", KeyType.BuiltIn)
  final val BINDER = Key("binder", KeyType.BuiltIn)
  final val BRACKET = Key("bracket", KeyType.BuiltIn)
  final val CELL = Key("cell", KeyType.BuiltIn)
  final val CELL_COLLECTION = Key("cellCollection", KeyType.BuiltIn)
  final val CELL_NAME = Key("cellName", KeyType.BuiltIn)
  final val COLOR = Key("color", KeyType.BuiltIn)
  final val COLORS = Key("colors", KeyType.BuiltIn)
  final val COMM = Key("comm", KeyType.BuiltIn)
  final val CONCRETE = Key("concrete", KeyType.BuiltIn)
  final val CONSTRUCTOR = Key("constructor", KeyType.BuiltIn)
  final val CONTEXT = Key("context", KeyType.BuiltIn)
  final val COOL = Key("cool", KeyType.BuiltIn)
  final val ELEMENT = Key("element", KeyType.BuiltIn)
  final val EXIT = Key("exit", KeyType.BuiltIn)
  final val FORMAT = Key("format", KeyType.BuiltIn)
  final val FRESH_GENERATOR = Key("freshGenerator", KeyType.BuiltIn)
  final val FUNCTION = Key("function", KeyType.BuiltIn)
  final val FUNCTIONAL = Key("functional", KeyType.BuiltIn)
  final val GROUP = Key("group", KeyType.BuiltIn)
  final val HEAT = Key("heat", KeyType.BuiltIn)
  final val HYBRID = Key("hybrid", KeyType.BuiltIn)
  final val HOOK = Key("hook", KeyType.BuiltIn)
  final val IDEM = Key("idem", KeyType.BuiltIn)
  final val IMPURE = Key("impure", KeyType.BuiltIn)
  final val INDEX = Key("index", KeyType.BuiltIn)
  final val INITIAL = Key("initial", KeyType.BuiltIn)
  final val INITIALIZER = Key("initializer", KeyType.BuiltIn)
  final val INJECTIVE = Key("injective", KeyType.BuiltIn)
  final val INTERNAL = Key("internal", KeyType.BuiltIn)
  final val KAST = Key("kast", KeyType.BuiltIn)
  final val KLABEL = Key("klabel", KeyType.BuiltIn)
  final val KORE = Key("kore", KeyType.BuiltIn)
  final val LABEL = Key("label", KeyType.BuiltIn)
  final val LATEX = Key("latex", KeyType.BuiltIn)
  final val LEFT = Key("left", KeyType.BuiltIn)
  final val LEMMA = Key("lemma", KeyType.BuiltIn)
  final val LOCATIONS = Key("locations", KeyType.BuiltIn)
  final val MACRO = Key("macro", KeyType.BuiltIn)
  final val MACRO_REC = Key("macro-rec", KeyType.BuiltIn)
  final val MAINCELL = Key("maincell", KeyType.BuiltIn)
  final val MEMO = Key("memo", KeyType.BuiltIn)
  final val ML_BINDER = Key("mlBinder", KeyType.BuiltIn)
  final val ML_OP = Key("mlOp", KeyType.BuiltIn)
  final val MULTIPLICITY = Key("multiplicity", KeyType.BuiltIn)
  final val NO_THREAD = Key("noThread", KeyType.BuiltIn)
  final val NON_ASSOC = Key("non-assoc", KeyType.BuiltIn)
  final val NON_EXECUTABLE = Key("non-executable", KeyType.BuiltIn)
  final val NOT_LR1 = Key("not-lr1", KeyType.BuiltIn)
  final val ONE_PATH = Key("one-path", KeyType.BuiltIn)
  final val OWISE = Key("owise", KeyType.BuiltIn)
  final val PARSER = Key("parser", KeyType.BuiltIn)
  final val PREC = Key("prec", KeyType.BuiltIn)
  final val PREFER = Key("prefer", KeyType.BuiltIn)
  final val PRIORITY = Key("priority", KeyType.BuiltIn)
  final val PRIVATE = Key("private", KeyType.BuiltIn)
  final val PUBLIC = Key("public", KeyType.BuiltIn)
  final val RESULT = Key("result", KeyType.BuiltIn)
  final val RETURNS_UNIT = Key("returnsUnit", KeyType.BuiltIn)
  final val RIGHT = Key("right", KeyType.BuiltIn)
  final val SEQSTRICT = Key("seqstrict", KeyType.BuiltIn)
  final val SIMPLIFICATION = Key("simplification", KeyType.BuiltIn)
  final val SMTLIB = Key("smtlib", KeyType.BuiltIn)
  final val SMT_HOOK = Key("smt-hook", KeyType.BuiltIn)
  final val SMT_LEMMA = Key("smt-lemma", KeyType.BuiltIn)
  final val STREAM = Key("stream", KeyType.BuiltIn)
  final val STRICT = Key("strict", KeyType.BuiltIn)
  final val SYMBOL = Key("symbol", KeyType.BuiltIn)
  final val SYMBOLIC = Key("symbolic", KeyType.BuiltIn)
  final val TAG = Key("tag", KeyType.BuiltIn)
  final val TOKEN = Key("token", KeyType.BuiltIn)
  final val TOPCELL = Key("topcell", KeyType.BuiltIn)
  final val TOTAL = Key("total", KeyType.BuiltIn)
  final val TRANSITION = Key("transition", KeyType.BuiltIn)
  final val TRUSTED = Key("trusted", KeyType.BuiltIn)
  final val TYPE = Key("type", KeyType.BuiltIn)
  final val UNBLOCK = Key("unblock", KeyType.BuiltIn)
  final val UNBOUND_VARIABLES = Key("unboundVariables", KeyType.BuiltIn)
  final val UNIT = Key("unit", KeyType.BuiltIn)
  final val UNPARSE_AVOID = Key("unparseAvoid", KeyType.BuiltIn)
  final val UNUSED = Key("unused", KeyType.BuiltIn)
  final val WRAP_ELEMENT = Key("wrapElement", KeyType.BuiltIn)

  /*
   * Internal attribute keys which cannot appear in user source code
   */
  final val ANONYMOUS = Key("anonymous", KeyType.Internal)
  final val BRACKET_LABEL = Key("bracketLabel", KeyType.Internal)
  final val CELL_FRAGMENT = Key("cellFragment", KeyType.Internal)
  final val CELL_OPT_ABSENT = Key("cellOptAbsent", KeyType.Internal)
  final val CELL_SORT = Key("cellSort", KeyType.Internal)
  final val CONCAT = Key("concat", KeyType.Internal)
  final val CONTENT_START_COLUMN = Key("contentStartColumn", KeyType.Internal)
  final val CONTENT_START_LINE = Key("contentStartLine", KeyType.Internal)
  final val COOL_LIKE = Key("cool-like", KeyType.Internal)
  final val DENORMAL = Key("denormal", KeyType.Internal)
  final val DIGEST = Key("digest", KeyType.Internal)
  final val DUMMY_CELL = Key("dummy_cell", KeyType.Internal)
  final val FILTER_ELEMENT = Key("filterElement", KeyType.Internal)
  final val FRESH = Key("fresh", KeyType.Internal)
  final val GENERATED_BY_LIST_SUBSORTING = Key("generatedByListSubsorting", KeyType.Internal)
  final val HAS_DOMAIN_VALUES = Key("hasDomainValues", KeyType.Internal)
  final val LOCATION = Key("org.kframework.attributes.Location", KeyType.Internal)
  final val NAT = Key("nat", KeyType.Internal)
  final val NOT_INJECTION = Key("notInjection", KeyType.Internal)
  final val ORIGINAL_NAME = Key("originalName", KeyType.Internal)
  final val ORIGINAL_PRD = Key("originalPrd", KeyType.Internal)
  final val PATTERN = Key("pattern", KeyType.Internal)
  final val PATTERN_FOLDING = Key("pattern-unfolding", KeyType.Internal)
  final val PREDICATE = Key("predicate", KeyType.Internal)
  final val PRETTY_PRINT_WITH_SORT_ANNOTATION = Key("prettyPrintWithSortAnnotation", KeyType.Internal)
  final val PRIORITIES = Key("priorities", KeyType.Internal)
  final val PRODUCTION = Key("org.kframework.definition.Production", KeyType.Internal)
  final val PRODUCTION_ID = Key("productionId", KeyType.Internal)
  final val PROJECTION = Key("projection", KeyType.Internal)
  final val RECORD_PRD = Key("recordPrd", KeyType.Internal)
  final val RECORD_PRD_ZERO = Key("recordPrd-zero", KeyType.Internal)
  final val RECORD_PRD_ONE = Key("recordPrd-one", KeyType.Internal)
  final val RECORD_PRD_MAIN = Key("recordPrd-main", KeyType.Internal)
  final val RECORD_PRD_EMPTY = Key("recordPrd-empty", KeyType.Internal)
  final val RECORD_PRD_SUBSORT = Key("recordPrd-subsort", KeyType.Internal)
  final val RECORD_PRD_REPEAT = Key("recordPrd-repeat", KeyType.Internal)
  final val RECORD_PRD_ITEM = Key("recordPrd-item", KeyType.Internal)
  final val REFRESHED = Key("refreshed", KeyType.Internal)
  final val REGEX = Key("regex", KeyType.Internal)
  final val REJECT = Key("reject", KeyType.Internal)
  final val REMOVE = Key("remove", KeyType.Internal)
  final val SMT_PRELUDE = Key("smt-prelude", KeyType.Internal)
  final val SORT = Key("org.kframework.kore.Sort", KeyType.Internal)
  final val SORT_PARAMS = Key("sortParams", KeyType.Internal)
  final val SOURCE = Key("org.kframework.attributes.Source", KeyType.Internal)
  final val SYNTAX_MODULE = Key("syntaxModule", KeyType.Internal)
  final val TEMPORARY_CELL_SORT_DECL = Key("temporary-cell-sort-decl", KeyType.Internal)
  final val TERMINALS = Key("terminals", KeyType.Internal)
  final val UNIQUE_ID = Key("UNIQUE_ID", KeyType.Internal)
  final val USER_LIST = Key("userList", KeyType.Internal)
  final val USER_LIST_TERMINATOR = Key("userListTerminator", KeyType.Internal)
  final val WITH_CONFIG = Key("withConfig", KeyType.Internal)

  private val stringClassName = classOf[String].getName
  private val intClassName = classOf[java.lang.Integer].getName

  // All Key fields with UPPER_CASE naming
  private val keys: Set[Key] =
    Att.getClass.getDeclaredFields
      .filter(f => f.getType.equals(classOf[Key]) && f.getName.matches("[A-Z]+(_[A-Z0-9]+)*"))
      .map(f => f.get(this).asInstanceOf[Key])
      .toSet

  def getBuiltinKeyOptional(key: String): Optional[Key] =
    if (keys.contains(Key(key, KeyType.BuiltIn))) {
      Optional.of(Key(key, KeyType.BuiltIn))
    } else {
      Optional.empty()
    }

  def getInternalKeyOptional(key: String): Optional[Key] =
    if (keys.contains(Key(key, KeyType.Internal))) {
      Optional.of(Key(key, KeyType.Internal))
    } else {
      Optional.empty()
    }

  def getUserGroupOptional(group: String) : Optional[Key] =
    if (!keys.contains(Key(group, KeyType.BuiltIn)) && !keys.contains(Key(group, KeyType.Internal))) {
      Optional.of(Key(group, KeyType.UserGroup))
    } else {
      Optional.empty()
    }

  private def getInternalKeyOrAssert(key: String): Key =
    getInternalKeyOptional(key).orElseThrow(() => 
        new AssertionError(
          "Key '" + key + "' was not found among the internal attributes whitelist.\n" + 
            "To add a new internal attribute, create a field `final val MY_ATT = Key(\"my-att\", KeyType.Internal)` " + 
            "in the Att object."))


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
      { case ((attKey, `stringClassName`), "") => attKey.key
        case ((attKey, _), value) => attKey.key + "(" + value + ")" } toList
  }
}
