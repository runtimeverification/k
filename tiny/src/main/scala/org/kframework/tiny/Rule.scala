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
      pmSolutions match {
        case OrChildren(children) if children.size == 0 =>
          //          println(" tried and failed " + left + " => " + right)
          Set()
        case OrChildren(children) => children map {
          case and =>
            processAnd(and)
        }
      }
    }
  }
}

object ExecuteRule {
  var count = 0
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory): K => Option[K] = {
    val left = RewriteToTop.toLeft(termWithRewrite)
    val right = RewriteToTop.toRight(termWithRewrite)

    def substitute(and: K, t: K): K = {
      assert(and.isPureSubsitution,
        "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
      Substitution(right).substitute(and.binding)
    }

    (t: K) => {


      //      print(count);
      count = count + 1;
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      pmSolutions match {
        case OrChildren(children) if children.size == 0 =>
          //          println(" tried and failed " + left + " => " + right)
          None
        case OrChildren(children) => children.headOption map {
          case and: K => substitute(and, t).normalize
        }
        case and: And => Some(substitute(and, t).normalize)
      }
    }
  }
}