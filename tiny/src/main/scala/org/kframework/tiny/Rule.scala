package org.kframework.tiny

object Rule {
  var count = 0
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory): Rule = {
    val left = RewriteToTop.toLeft(termWithRewrite).normalize
    val right = RewriteToTop.toRight(termWithRewrite).normalize

    def substitute(and: K, t: K): K = {
      assert(and.isPureSubsitution,
        "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
      Substitution(right).substitute(and.binding)
    }

    (t: K) => {

      def processAnd(and: K) = {
        val res = substitute(and, t).normalize
        println(" applied " + left + " => " + right);
        println(" resulting in " + res)
        res
      }

      //      print(count);
      count = count + 1;
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      AsOr(pmSolutions).children map processAnd
    }
  }
}

case class ExecuteRule(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory) extends (K => Option[K]) {
  val left = RewriteToTop.toLeft(termWithRewrite)
  val right = RewriteToTop.toRight(termWithRewrite)

  var count = 0

  def substitute(and: K, t: K): K = {
    assert(and.isPureSubsitution,
      "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
    Substitution(right).substitute(and.binding)
  }

  def apply(t: K) = {
    //      print(count);F
    val pmSolutions = And(left.matcher(t), sideConditions).normalize
    AsOr(pmSolutions).children.headOption map { count += 1; substitute(_, t).normalize }
  }
}