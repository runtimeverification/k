package org.kframework.parser.kore.parser

import org.kframework.parser.kore
import org.kframework.{kore => k}
import org.kframework.kore.KORE

/** Parsing error exception. */
case class TranslationError(msg: String) extends RuntimeException(msg) // ParseError.msg eq Exception.detailMessage, i.e., msg() == getMessage()

/** Conversion function from Kore to K. */

object KoreToK {

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
    if (head.params.length != 0)  {
      throw new TranslationError("Parameterized Heads currently unsupported")
    } else {
      KORE.KLabel(head.ctr)
    }
  }

  /** Returns a [[k.K]] from [[kore.Pattern]]. */
  def apply(pat: kore.Pattern): k.K = pat match {
    case kore.Variable(name, sort) =>
      KORE.KVariable(name, KORE.Att.add(classOf[k.Sort].toString, apply(sort).toString()))
    case kore.Application(head, args) =>
      KORE.KApply(apply(head), args.map((k) => apply(k)))
    case kore.Top(s) =>
      throw new TranslationError("Top patterns currently unsupported")
    case kore.Bottom(s) =>
      throw new TranslationError("Bottom patterns currently unsupported")
    case kore.And(s, p, q) =>
      throw new TranslationError("And patterns currently unsupported")
    case kore.Or(s, p, q) =>
      throw new TranslationError("Or patterns currently unsupported")
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
    // case Next(s, p) =>
    //   "\\next" + "{" + apply(s) + "}" +
    //     "(" + apply(p) + ")"
    case kore.Rewrites(s, p, q) =>
      KORE.KRewrite(apply(p), apply(q))
    case kore.Ceil(s, rs, p) =>
      throw new TranslationError("Ceil patterns currently unsupported")
    case kore.Floor(s, rs, p) =>
      throw new TranslationError("Floor patterns currently unsupported")
    case kore.Equals(s1, s2, p, q) =>
      throw new TranslationError("Floor patterns currently unsupported")
    case kore.Mem(s, rs, p, q) =>
      throw new TranslationError("Mem patterns currently unsupported")
    case kore.DomainValue(s, str) =>
      KORE.KToken(str, apply(s))
    case kore.StringLiteral(str) =>
      throw new TranslationError("String literal patterns currently unsupported")
  }
}
