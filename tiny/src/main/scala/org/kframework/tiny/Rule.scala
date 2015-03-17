package org.kframework.tiny

object Rule {
  var count = 0
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory): Rule = {
    val left = RewriteToTop.toLeft(termWithRewrite).normalize
    val right = RewriteToTop.toRight(termWithRewrite).normalize

    def substitute(and: And, t: K): K = {
      assert(and.isPureSubsitution,
        "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
      Substitution(right).substitute(and.binding)
    }

    (t: K) => {

      def processAnd(and: And) = {
        val res = substitute(and, t).normalize
        println(" applied " + left + " => " + right);
        println(" resulting in " + res)
        res
      }

//      print(count);
      count = count + 1;
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      pmSolutions match {
        case Or(children, _, _) if children.size == 0 =>
//          println(" tried and failed " + left + " => " + right)
          Set()
        case Or(children, _, _) => children map {
          case and: And =>
            processAnd(and)
        }
        case and: And => Set(processAnd(and))
      }
    }
  }
}

object ExecuteRule {
  var count = 0
  def apply(termWithRewrite: K, sideConditions: K = True)(implicit theory: Theory): K => Option[K] = {
    val left = RewriteToTop.toLeft(termWithRewrite)
    val right = RewriteToTop.toRight(termWithRewrite)

    def substitute(and: And, t: K): K = {
      assert(and.isPureSubsitution,
        "Invalid substitution when applying " + left + " to " + t + ":\n" + and)
      Substitution(right).substitute(and.binding)
    }

    (t: K) => {

      def processAnd(and: And) = {
        val res = substitute(and, t).normalize
//        println(" applied " + left + " => " + right);
//        println(" resulting in " + res)
        res
      }

//      print(count);
      count = count + 1;
      val pmSolutions = And(left.matcher(t), sideConditions).normalize
      pmSolutions match {
        case Or(children, _, _) if children.size == 0 =>
//          println(" tried and failed " + left + " => " + right)
          None
        case Or(children, _, _) => children.headOption map {
          case and: And =>
            processAnd(and)
        }
        case and: And => Some(processAnd(and))
      }
    }
  }
}