package org.kframework.tiny

trait Rule extends (K => Set[K]) {
  val termWithRewrite: K
  val sideConditions: K
  implicit val theory: Theory

  val left = RewriteToTop.toLeft(termWithRewrite)
  val right = RewriteToTop.toRight(termWithRewrite)

  var count = 0

  def substitute(and: K, t: K): K = {
    assert(and.isPureSubsitution,
      "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
    Substitution(right).substitute(and.binding)
  }

  def matchTerm(t: K) = And(left.matcher(t), sideConditions).normalize

}

case class RegularRule(termWithRewrite: K, sideConditions: K)(implicit val theory: Theory) extends Rule {

  def apply(t: K) = {
    val pmSolutions = matchTerm(t)
    AsOr(pmSolutions).children map { count += 1; substitute(_, t).normalize }
  }
}

case class AnywhereRule(termWithRewrite: K, sideConditions: K)(implicit val theory: Theory) extends Rule {

  val regularRule = RegularRule(termWithRewrite, sideConditions)

  def recursiveResults(t: K): Set[K] = t match {
    case kapp: KAssocApp => {
      val childResults = kapp.children map recursiveResults

      val resultsFromChldren = childResults
        .foldLeft(Set(Seq[K]())) {(soFar, nextArg) => soFar flatMap {args => nextArg map { args :+ _ } } }
        .map { kapp.klabel(_: _*) }

      val ignorePrefixVar = KVar("IGNORED_PREFIX")
      val ignoreSuffixVar = KVar("IGNORED_SUFFIX")

      val rule = RegularRule(kapp.klabel(ignorePrefixVar, termWithRewrite, ignoreSuffixVar), sideConditions)

      resultsFromChldren | rule(t)
    }
    case kapp: KApp =>
      val childResults = kapp.children map recursiveResults

      val resultsFromChldren = childResults
        .foldLeft(Set(Seq[K]())) {(soFar, nextArg) => soFar flatMap {args => nextArg map { args :+ _ } } }
        .map { kapp.klabel(_: _*) }

      resultsFromChldren | regularRule(t)
    case other => regularRule(t)
  }

  def apply(t: K) = {
    recursiveResults(t)
  }
}

case class ExecuteRule(termWithRewrite: K, sideConditions: K = True)(implicit val theory: Theory) extends Rule {
  def apply(t: K) = {
    val pmSolutions = matchTerm(t)
    AsOr(pmSolutions).children.headOption map { count += 1; substitute(_, t).normalize } toSet
  }
}
