package org.kframework.tiny

import org.kframework.tiny.builtin.Bag

trait Rule extends (K => Set[K])

trait FromKDef {
  val termWithRewrite: K
  val sideConditions: K
  implicit val theory: Theory

  val left = RewriteToTop.toLeft(termWithRewrite)
  val right = RewriteToTop.toRight(termWithRewrite)

  override def toString = "===[ rl " + termWithRewrite + " ]===>"

  var count = 0

  def substitute(and: K, t: K): K = {
    assert(and.isPureSubsitution,
      "Invalid substitution when applying " + left + " to " + t + ":\n" + AsAnd(and).children.map(x => x + " of type " + x.getClass).mkString("\n"))
    Substitution(right).substitute(and.binding)
  }

  def matchTerm(t: K) = {
    val tWithFreshVars = if (!t.isGround)
      RenameVariables(t)
    else
      t

    And(left.matcher(tWithFreshVars), sideConditions).normalize
  }
}

case class RegularRule(termWithRewrite: K, sideConditions: K)(implicit val theory: Theory)
  extends Rule with FromKDef {
  def apply(t: K) = {
    val pmSolutions = matchTerm(t)
    AsOr(pmSolutions).children map {
      count += 1;
      substitute(_, t).normalize
    }
  }
}

case class AnywhereRule(termWithRewrite: K, sideConditions: K)(implicit val theory: Theory)
  extends Rule with FromKDef {

  val regularRule = RegularRule(termWithRewrite, sideConditions)

  val ignorePrefixVar = KVar("IGNORED_PREFIX")
  val ignoreSuffixVar = KVar("IGNORED_SUFFIX")

  def recursiveResults(t: K): Set[K] = (left, t) match {
    case (left: Bag, kapp: Bag) if kapp.klabel == left.klabel =>
      val ruleWithJustOneSide = RegularRule(kapp.klabel(ignorePrefixVar, termWithRewrite), sideConditions)
      process(kapp) | ruleWithJustOneSide(t)

    case (left: KAssocApp, kapp: KAssocApp) if kapp.klabel == left.klabel => {
      val ruleWithSides = RegularRule(kapp.klabel(ignorePrefixVar, termWithRewrite, ignoreSuffixVar), sideConditions)
      process(kapp) | ruleWithSides(t)
    }
    case (left: K, kapp: KApp) => process(kapp) | regularRule(t)
    case other => regularRule(t)
  }

  def process(kapp: KApp): Set[K] = {
    kapp.children
      .map(recursiveResults)
      .foldLeft(Set(Seq[K]())) { (soFar, nextArg) => soFar flatMap { args => nextArg map {
      args :+ _
    }
    }
    }
      .map {
      kapp.klabel(_: _*)
    }
  }

  def apply(t: K) = {
    recursiveResults(t)
  }
}

case class EverywhereRule(termWithRewrite: K, sideConditions: K)(implicit val theory: Theory)
  extends Rule with FromKDef {

  val regularRule = RegularRule(termWithRewrite, sideConditions)
  val ignorePrefixVar = KVar("IGNORED_PREFIX")
  val ignoreSuffixVar = KVar("IGNORED_SUFFIX")

  def recursiveResults(t: K): K = (left, t) match {
    case (left: Bag, kapp: Bag) if kapp.klabel == left.klabel =>
      val ruleWithJustOneSide = RegularRule(kapp.klabel(ignorePrefixVar, termWithRewrite), sideConditions)
      process(ruleWithJustOneSide(t).head.asInstanceOf[KApp])

    case (left: KAssocApp, kapp: KAssocApp) if kapp.klabel == left.klabel => {
      val ruleWithSides = RegularRule(kapp.klabel(ignorePrefixVar, termWithRewrite, ignoreSuffixVar), sideConditions)
      process(ruleWithSides(t).head.asInstanceOf[KApp])
    }
    case (left: K, kapp: KApp) => process(kapp)
    case other => regularRule(t).headOption.getOrElse(t)
  }

  def process(kapp: KApp): K = {
    val partialResult = kapp.klabel(kapp.children.map(recursiveResults).toSeq: _*)
    regularRule(partialResult).headOption.getOrElse(partialResult)
  }

  def apply(t: K): Set[K] = {
    Set(recursiveResults(t))
  }
}

case class ExecuteRule(termWithRewrite: K, sideConditions: K = True)(implicit val theory: Theory)
  extends Rule with FromKDef {
  def apply(t: K) = {
    val pmSolutions = matchTerm(t)
    if (pmSolutions.isPureSubsitution) {
      AsOr(pmSolutions).children.headOption map {
        count += 1;
        substitute(_, t).normalize
      } toSet
    } else
      Set()
  }
}
