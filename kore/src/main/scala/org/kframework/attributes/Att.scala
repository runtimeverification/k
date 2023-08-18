// Copyright (c) K Team. All Rights Reserved.
package org.kframework.attributes

import java.util.Optional
import java.util.regex.Pattern
import org.kframework.Collections._
import org.kframework.definition._
import org.kframework.kore.Sort
import org.kframework.utils.errorsystem.KEMException

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
 * - We use a wrapper Att.Key(String,KeyType) rather than a raw String key. This helps to enforce access controls and
 *   allows for easier IDE navigation to where each attribute is used.
 *
 * New attributes should be added as a Key field Att.MY_NEW_ATT in the object below.
 *
 * To obtain an appropriate Key, use
 * - Att.MY_ATT, if you statically know the key you want
 * - Att.getBuiltInKeyOptional(myAttStr), if checking a user-supplied attribute string. Be sure to report an error
 *   if the lookup fails
 * - Att.getInternalKeyOptional(myAttStr), if expecting an internal key
 * - Att.getUserGroupOptional(myAttStr), if expecting a user-group, enforcing that it is not a built-in
 * 
 * During parsing, you may also use Att.unrecognizedKey(myAttStr) to delay error reporting on an unrecognized attribute
 */
class Att private (val att: Map[(Att.Key, String), Any]) extends AttributesToString with Serializable {

  override lazy val hashCode: Int = att.hashCode()
  override def equals(that: Any): Boolean = that match {
    case a: Att => a.att == att
    case _ => false
  }

  // Remove all UserGroups and replace them with a group(_) attribute
  def withUserGroupsAsGroupAtt: Att = {
    val groups = att.keys.filter(_._1.keyType.equals(Att.KeyType.UserGroup)).toSet;
    if (groups.isEmpty)
      this
    else
      Att(att -- groups).add(Att.GROUP, groups.map(_._1.key).mkString(","))
  }

  // Remove the group(_) attribute and insert each of its arguments as a UserGroup
  // Returns either Left of an error message or Right of the result
  def withGroupAttAsUserGroups: Either[String, Att] = {
    if (!contains(Att.GROUP, classOf[String]))
      return Right(this)
    val groups = get(Att.GROUP).trim
    if (groups.isEmpty)
      return Left("group(_) attribute expects a comma-separated list of arguments.")
    val badComma = Left("Extraneous ',' in group(_) attribute.")
    if (groups.startsWith(",") || groups.endsWith(","))
      return badComma
    var att = this
    for (group <- groups.split("\\s*,\\s*")) {
      if (group.isEmpty)
        return badComma
      val groupKey = Att.getUserGroupOptional(group)
      if (groupKey.isEmpty)
        return Left("User-defined group '" + group + "' conflicts with a built-in attribute.")
      if (!group.matches("[a-z][a-zA-Z0-9-]*"))
        return Left("Invalid argument '" + group + "' in group(_) attribute. " +
          "Expected a lower case letter followed by any number of alphanumeric or '-' characters.")
      att = att.add(groupKey.get)
    }
    Right(att.remove(Att.GROUP))
  }
  val unrecognizedKeys: Set[Att.Key] =
    att.map(_._1._1).filter(_.keyType.equals(Att.KeyType.Unrecognized)).toSet

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

  private def add[T <: AttValue](key: Att.Key, clsStr: String, value: T): Att = key.keyParam match {
    case Att.KeyParameter.Forbidden => throwForbidden(key)
    case _ => Att(att + ((key, clsStr) -> value))
  }
  private def add(key: Att.Key, clsStr: String, value: String): Att = key.keyParam match {
    case Att.KeyParameter.Forbidden if value != "" => throwForbidden(key)
    case Att.KeyParameter.Required  if value == "" => throwRequired(key)
    case _ => Att(att + ((key, clsStr) -> value))
  }
  private def add(key: Att.Key, clsStr: String, value: Int): Att = key.keyParam match {
    case Att.KeyParameter.Forbidden => throwForbidden(key)
    case _ => Att(att + ((key, clsStr) -> value))
  }

  private def throwRequired(key: Att.Key) = throw KEMException.compilerError("Parameters for the attribute '" + key + "' are required.")
  private def throwForbidden(key: Att.Key) = throw KEMException.compilerError("Parameters for the attribute '" + key + "' are forbidden.")

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
    // Attributes which represent user-defined groups via group(_).
    //
    // WARNING: Although we treat the arguments to group(_) as individual attributes internally,
    // for any external interface (emitting KORE, JSON, etc.), we must re-emit them under the group(_) attribute,
    // else there will be conflicts when a user group has the same name as an internal attribute.
    case object UserGroup extends KeyType;
    // Attributes from user source code which are not recognized as built-ins
    // This is only used to delay error reporting until after parsing, allowing us to report multiple errors
    case object Unrecognized extends KeyType;
  }

  sealed trait KeyParameter
  private object KeyParameter extends Serializable {
    case object Required extends KeyParameter;
    case object Optional extends KeyParameter;
    case object Forbidden extends KeyParameter;
  }

  /* The Key class can only be constructed within Att. To enforce this, we must
   * - Make the constructor private
   * - Manually declare apply() and make it private, lest a public one is generated
   * - Manually declare copy() and make it private, preventing constructions like Att.GOOD_KEY.copy(key="bad-att")
   */
  case class Key private[Att](key: String, keyType: KeyType, keyParam: KeyParameter, allowedSentences: Set[Class[_]]) extends Serializable {
    override def toString: String = key
    private[Key] def copy(): Unit = ()
  }
  object Key {
    private[Att] def apply(key: String, keyType: KeyType): Key = Key(key, keyType, KeyParameter.Optional)
    private[Att] def apply(key: String, keyType: KeyType, keyParam: KeyParameter): Key = Key(key, keyType, keyParam, Set(classOf[AnyRef]))
    private[Att] def apply(key: String, keyType: KeyType, keyParam: KeyParameter, allowedSentences: Set[Class[_]]): Key = new Key(key, keyType, keyParam, allowedSentences)
  }

  def unrecognizedKey(key: String): Att.Key =
    Att.Key(key, KeyType.Unrecognized)

  val empty: Att = Att(Map.empty)

  /*
   * Built-in attribute keys which can appear in user source code
   */
  final val ALIAS = Key("alias", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[Rule]))
  final val ALIAS_REC = Key("alias-rec", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[Rule]))
  final val ALL_PATH = Key("all-path", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Claim]))
  final val ANYWHERE = Key("anywhere", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val APPLY_PRIORITY = Key("applyPriority", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val ASSOC = Key("assoc", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val AVOID = Key("avoid", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val BAG = Key("bag", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val BINDER = Key("binder", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val BRACKET = Key("bracket", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val CELL = Key("cell", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val CELL_COLLECTION = Key("cellCollection", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[SyntaxSort]))
  final val CELL_NAME = Key("cellName", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val CIRCULARITY = Key("circularity", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Claim]))
  final val COLOR = Key("color", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val COLORS = Key("colors", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val COMM = Key("comm", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val CONCRETE = Key("concrete", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Module], classOf[Production], classOf[Rule]))
  final val CONSTRUCTOR = Key("constructor", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val CONTEXT = Key("context", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[ContextAlias]))
  final val COOL = Key("cool", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val DEPENDS = Key("depends", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Claim]))
  final val ELEMENT = Key("element", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val EXIT = Key("exit", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val FORMAT = Key("format", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val FRESH_GENERATOR = Key("freshGenerator", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val FUNCTION = Key("function", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val FUNCTIONAL = Key("functional", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val GROUP = Key("group", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Sentence]))
  final val HASKELL = Key("haskell", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Module]))
  final val HEAT = Key("heat", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val HOOK = Key("hook", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production], classOf[SyntaxSort]))
  final val HYBRID = Key("hybrid", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val IDEM = Key("idem", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val IMPURE = Key("impure", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val INDEX = Key("index", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val INITIAL = Key("initial", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val INITIALIZER = Key("initializer", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[Rule]))
  final val INJECTIVE = Key("injective", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val INTERNAL = Key("internal", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val KAST = Key("kast", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Module]))
  final val KLABEL = Key("klabel", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val KORE = Key("kore", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[RuleOrClaim], classOf[Module]))
  final val LABEL = Key("label", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Sentence]))
  final val LATEX = Key("latex", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val LEFT = Key("left", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val LOCATIONS = Key("locations", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[SyntaxSort]))
  final val MACRO = Key("macro", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[Rule]))
  final val MACRO_REC = Key("macro-rec", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production], classOf[Rule]))
  final val MAINCELL = Key("maincell", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val MEMO = Key("memo", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val ML_BINDER = Key("mlBinder", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val ML_OP = Key("mlOp", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val MULTIPLICITY = Key("multiplicity", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val NON_ASSOC = Key("non-assoc", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val NON_EXECUTABLE = Key("non-executable", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val NOT_LR1 = Key("not-lr1", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Module]))
  final val NO_EVALUATORS = Key("no-evaluators", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val ONE_PATH = Key("one-path", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Claim]))
  final val OWISE = Key("owise", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val PARSER = Key("parser", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val PREC = Key("prec", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val PREFER = Key("prefer", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val PRESERVES_DEFINEDNESS = Key("preserves-definedness", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val PRIORITY = Key("priority", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Rule]))
  final val PRIVATE = Key("private", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Module], classOf[Production]))
  final val PUBLIC = Key("public", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Module], classOf[Production]))
  final val RESULT = Key("result", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[ContextAlias], classOf[Context], classOf[Rule]))
  final val RETURNS_UNIT = Key("returnsUnit", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val RIGHT = Key("right", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val SEQSTRICT = Key("seqstrict", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val SIMPLIFICATION = Key("simplification", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Rule]))
  final val SMTLIB = Key("smtlib", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val SMT_HOOK = Key("smt-hook", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val SMT_LEMMA = Key("smt-lemma", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val STREAM = Key("stream", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Rule]))
  final val STRICT = Key("strict", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Production]))
  final val STRUCTURAL = Key("structural", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Rule]))
  final val SYMBOL = Key("symbol", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val SYMBOLIC = Key("symbolic", KeyType.BuiltIn, KeyParameter.Optional, Set(classOf[Module], classOf[Production], classOf[Rule]))
  final val TAG = Key("tag", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Rule]))
  final val TOKEN = Key("token", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[SyntaxSort], classOf[Production]))
  final val TOTAL = Key("total", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val TRUSTED = Key("trusted", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Claim]))
  final val TYPE = Key("type", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val UNBOUND_VARIABLES = Key("unboundVariables", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[RuleOrClaim]))
  final val UNIT = Key("unit", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))
  final val UNPARSE_AVOID = Key("unparseAvoid", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val UNUSED = Key("unused", KeyType.BuiltIn, KeyParameter.Forbidden, Set(classOf[Production]))
  final val WRAP_ELEMENT = Key("wrapElement", KeyType.BuiltIn, KeyParameter.Required, Set(classOf[Production]))

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
  final val LOCATION = Key(classOf[Location].getName, KeyType.Internal)
  final val NAT = Key("nat", KeyType.Internal)
  final val NOT_INJECTION = Key("notInjection", KeyType.Internal)
  final val NOT_LR1_MODULES = Key("not-lr1-modules", KeyType.Internal)
  final val ORIGINAL_NAME = Key("originalName", KeyType.Internal)
  final val ORIGINAL_PRD = Key("originalPrd", KeyType.Internal)
  final val PATTERN = Key("pattern", KeyType.Internal)
  final val PATTERN_FOLDING = Key("pattern-folding", KeyType.Internal)
  final val PREDICATE = Key("predicate", KeyType.Internal)
  final val PRETTY_PRINT_WITH_SORT_ANNOTATION = Key("prettyPrintWithSortAnnotation", KeyType.Internal)
  final val PRIORITIES = Key("priorities", KeyType.Internal)
  final val PRODUCTION = Key(classOf[Production].getName, KeyType.Internal)
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
  final val SORT = Key(classOf[Sort].getName, KeyType.Internal)
  final val SORT_PARAMS = Key("sortParams", KeyType.Internal)
  final val SOURCE = Key(classOf[Source].getName, KeyType.Internal)
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
  private val pat = Pattern.compile("[A-Z]+(_[A-Z0-9]+)*")
  private val keys: Map[String, Key] =
    Att.getClass.getDeclaredFields
      .filter(f => f.getType.equals(classOf[Key]) && pat.matcher(f.getName).matches())
      .map(f => f.get(this).asInstanceOf[Key])
      .map(k => (k.key, k))
      .toMap

  private val builtinKeys: Set[String] = keys.filter(_._2.keyType == KeyType.BuiltIn).keySet
  private val internalKeys: Set[String] = keys.filter(_._2.keyType == KeyType.Internal).keySet

  def getBuiltinKeyOptional(key: String): Optional[Key] =
    if (builtinKeys.contains(key)) {
      Optional.of(keys.get(key).get)
    } else {
      Optional.empty()
    }

  def getInternalKeyOptional(key: String): Optional[Key] =
    if (internalKeys.contains(key)) {
      Optional.of(keys.get(key).get)
    } else {
      Optional.empty()
    }

  def getUserGroupOptional(group: String) : Optional[Key] =
    if (!builtinKeys.contains(group)) {
      Optional.of(Key(group, KeyType.UserGroup, KeyParameter.Optional))
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
