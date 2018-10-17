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
          KORE.Sort(ctr)
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

  /** Returns a [[k.K]] from [[kore.Pattern]]. */
  def apply(pat: kore.Pattern): k.K = pat match {
    case kore.Variable(name, sort) =>
      KORE.KVariable(name, KORE.Att.add(classOf[k.Sort].toString, apply(sort).toString()))
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
      throw new TranslationError("Not patterns currently unsupported")
    case kore.Implies(s, p, q) =>
      throw new TranslationError("Implies patterns currently unsupported")
    case kore.Iff(s, p, q) =>
      throw new TranslationError("Iff patterns currently unsupported")
    case kore.Exists(s, v, p) =>
      throw new TranslationError("Exists patterns currently unsupported")
    case kore.Forall(s, v, p) =>
      throw new TranslationError("Forall patterns currently unsupported")
    case kore.Rewrites(s, p, q) =>
      KORE.KRewrite(apply(p), apply(q))
    case kore.Ceil(s, rs, p) =>
      throw new TranslationError("Ceil patterns currently unsupported")
    case kore.Floor(s, rs, p) =>
      throw new TranslationError("Floor patterns currently unsupported")
    case kore.Equals(s1, s2, p, q) =>
      KORE.KApply(KLabels.EQUALS_K, apply(p), apply(q))
    case kore.Mem(s, rs, p, q) =>
      throw new TranslationError("Mem patterns currently unsupported")
    case kore.DomainValue(s, str) =>
      KORE.KToken(if (sortAtt.get(apply(s)).getOrElse(KORE.Att).getOptional("hook").orElse("") == "STRING.String") enquote(str) else str, apply(s))
    case kore.StringLiteral(str) =>
      KORE.KToken(str, Sorts.KString)
  }
}
