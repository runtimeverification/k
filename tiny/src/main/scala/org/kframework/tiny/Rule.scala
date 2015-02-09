package org.kframework.tiny

object Rule {
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory = FreeTheory): Rule = {
    val left = RewriteToTop.toLeft(termWithRewrite)
    val right = RewriteToTop.toRight(termWithRewrite)

    (t: K) => {
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      pmSolutions match {
        case Or(children, _) => children map {
          case and: And => Substitution(right).substitute(and.binding)
        }
        case and: And => Set(Substitution(right).substitute(and.binding))
      }
    }
  }
}
