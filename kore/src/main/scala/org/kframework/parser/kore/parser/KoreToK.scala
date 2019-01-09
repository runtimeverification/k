package org.kframework.parser.kore.parser

import org.kframework.builtin.{KLabels, Sorts}
import org.kframework.kore.KORE
import org.kframework.attributes.Att
import org.kframework.parser.kore
import org.kframework.{kore => k}

import scala.collection.Map
import scala.collection.JavaConverters._

/** Translation error exception. */
case class TranslationError(msg: String) extends RuntimeException(msg)

/** Conversion function from Kore to K. */

class KoreToK (headToLabel_ : java.util.Properties, sortAtt : Map[k.Sort, Att], enquote: String => String) {

  val koreToKLabel = headToLabel_.asScala.toMap;

  /** Returns a [[k.Sort]] from [[kore.Sort]]. */
  def apply(s: kore.Sort): k.Sort = s match {
      case kore.SortVariable(name) =>
        throw new TranslationError("Unexpected Sort Variable")
      case kore.CompoundSort(ctr, params) =>
        if (params.length != 0) {
          throw new TranslationError("Parameterized sorts currently unsupported")
        } else {
          assert(ctr.startsWith("Sort"))
          KORE.Sort(ctr.substring( 4));
        }
  }

  /** Returns a [[k.KLabel]] from [[kore.SymbolOrAlias]] */
  def apply(head: kore.SymbolOrAlias): k.KLabel = {
    KORE.KLabel(extractKLabel(head.ctr), head.params.map(p => apply(p)): _*)
  }

  private def extractKLabel(head: String): String = {
    if (head.startsWith("Lbl")) {
      extractKLabel(head.substring(3))
    } else {
      koreToKLabel.applyOrElse(head, Function.const(head))
    }
  }

  private def extractVarName(name: String): String = {
    if (name.startsWith("Var")) {
      name.substring(3)
    } else {
      name
    }
  }

  /** Returns a [[k.K]] from [[kore.Pattern]]. */
  def apply(pat: kore.Pattern): k.K = pat match {
    case kore.Variable(name, sort) =>
      KORE.KVariable(extractVarName(name), KORE.Att.add(classOf[k.Sort].toString, apply(sort).toString()))
    case kore.Application(head, args) => head.ctr match {
      case "inj" =>
        apply(args.head)
      case "kseq" =>
        KORE.KSequence(args.map(apply(_)): _*)
      case "dotk" =>
        KORE.KSequence()
      case _ =>
        KORE.KApply(apply(head), args.map((k) => apply(k)))
    }
    case kore.Top(s) =>
      KORE.KApply(KLabels.ML_TRUE)
    case kore.Bottom(s) =>
      KORE.KApply(KLabels.ML_FALSE)
    case kore.And(s, p, q) =>
      KORE.KApply(KLabels.ML_AND, apply(p), apply(q))
    case kore.Or(s, p, q) =>
      KORE.KApply(KLabels.ML_OR, apply(p), apply(q))
    case kore.Not(s, p) =>
      KORE.KApply(KLabels.ML_NOT, apply(p))
    case kore.Implies(s, p, q) =>
      KORE.KApply(KLabels.ML_IMPLIES, apply(p), apply(q))
    case kore.Iff(s, p, q) =>
      throw new TranslationError("Iff patterns currently unsupported")
    case kore.Exists(s, v, p) =>
      KORE.KApply(KLabels.ML_EXISTS, apply(v), apply(p))
    case kore.Forall(s, v, p) =>
      KORE.KApply(KLabels.ML_FORALL, apply(v), apply(p))
    case kore.Rewrites(s, p, q) =>
      KORE.KRewrite(apply(p), apply(q))
    case kore.Ceil(s, rs, p) =>
      KORE.KApply(KLabels.ML_CEIL, apply(p))
    case kore.Floor(s, rs, p) =>
      throw new TranslationError("Floor patterns currently unsupported")
    case kore.Equals(s1, s2, p, q) =>
      KORE.KApply(KLabels.ML_EQUALS, apply(p), apply(q))
    case kore.Mem(s, rs, p, q) =>
      throw new TranslationError("Mem patterns currently unsupported")
    case kore.DomainValue(s, str) =>
      KORE.KToken(if (sortAtt.get(apply(s)).getOrElse(KORE.Att).getOptional("hook").orElse("") == "STRING.String") enquote(str) else str, apply(s))
    case kore.StringLiteral(str) =>
      KORE.KToken(str, Sorts.KString)
  }
}
