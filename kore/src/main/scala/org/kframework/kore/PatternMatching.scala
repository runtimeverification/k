package org.kframework.kore

import KBoolean._
import KORE._

case class MatchException(m: String) extends RuntimeException(m)

trait BindingOps {

  def or(s1: Set[Map[KVariable, K]], s2: Set[Map[KVariable, K]]): Set[Map[KVariable, K]] =
    s1 | s2

  def and(s1: Set[Map[KVariable, K]], s2: Set[Map[KVariable, K]]): Set[Map[KVariable, K]] = {
    (for (m1 <- s1; m2 <- s2) yield {
      and(m1, m2)
    }).flatten
  }

  def and(m1: Map[KVariable, K], m2: Map[KVariable, K]): Option[Map[KVariable, K]] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((m1.keys.toSet & m2.keys.toSet).exists(v => m1(v) != m2(v))) {
      None
    } else
      Some(m1 ++ m2)
  }
}

trait Matcher {
  def m(pattern: K) = matchOne(pattern)
  /**
   * match a pattern
   */
  def matchOne(pattern: K, condition: K = true): Option[Map[KVariable, K]] = matchAll(pattern, condition).headOption

  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]]
}

trait KListMatcher extends Matcher with BindingOps {
  self: KList =>

  implicit def wrapKList(l: KList) = 'KList(l: _*)

  def matchAll(pattern: K, condition: K): Set[Map[KVariable, K]] = {
    (this: KList, pattern) match {
      case (_, v: KVariable) => Set(Map(v -> this))
      case (_, lP) if lP == 'KList(this: _*) => Set(Map())
      case (_, KApply(KLabel("KList"), klistP: KList, _)) =>
        (this, klistP) match {
          case (KList(), KList()) => Set(Map())
          case (head +: tail, headP +: tailP) if headP == head => tail.matchAll(tailP)
          case (_, (v: KVariable) +: tailP) =>
            (0 to size)
              .map { index => (take(index), drop(index)) }
              .map {
                case (prefix, suffix) =>
                  and(Set(Map(v -> (prefix: K))), suffix.matchAll(tailP))
              }
              .fold(Set())(or)
          case _ => Set()
        }
    }
  }
}

trait KApplyMatcher extends Matcher with BindingOps {
  self: KApply =>

  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]] = (pattern, this: KApply) match {
    case (v: KVariable, _) =>
      Set(Map(v -> this))
    case (KApply(label, klist, att), KApply(label2, klist2, att2)) if label == label2 =>
      klist2.matchAll('KList(klist.toSeq: _*), condition)

    case (_: KApply, _: KApply) => Set()
  }
}

trait KVariableMatcher extends Matcher with BindingOps {
  self: KVariable =>

  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]] =
    throw MatchException("Encountered a KVariable on the object side during regular (non-symbolic) matching")
}

trait KRewriteMatcher extends Matcher with BindingOps {
  self: KRewrite =>

  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]] = (pattern, this: KRewrite) match {
    case (v: KVariable, _) =>
      Set(Map(v -> this))
  }
}

trait KTokenMatcher extends Matcher with BindingOps {
  self: KToken =>
  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]] = (pattern, this: KToken) match {
    case (v: KVariable, _) =>
      Set(Map(v -> this))
    case (KToken(`sort`, `s`, _), _) => Set(Map())
    case _ => Set()
  }
}

trait KSequenceMatcher extends Matcher with BindingOps {
  self: KSequence =>
  def matchAll(pattern: K, condition: K = true): Set[Map[KVariable, K]] = (pattern, this: KSequence) match {
    case (v: KVariable, _) =>
      Set(Map(v -> this))
    case (s: KSequence, _) =>
      klist.matchAll('KList(s.klist: _*), condition) map {
        case m: Map[KVariable, KApply] => m mapValues {
          case KApply(KLabel("KList"), kl, _) => KSequence(kl.toSeq: _*)
        }
      }
  }
}
