package org.kframework.tiny

object Rule {
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory = FreeTheory): Rule = {
    val left = RewriteToTop.toLeft(termWithRewrite)
    val right = RewriteToTop.toRight(termWithRewrite)

    def substitute(and: And, t: K): K = {
      assert(and.isPureSubsitution,
        "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
      Substitution(right).substitute(and.binding)
    }

    (t: K) => {
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      pmSolutions match {
        case Or(children, _, _) => children map {
          case and: And => substitute(and, t)
        }
        case and: And => Set(substitute(and, t))
      }
    }
  }
}
