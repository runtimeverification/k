package org.kframework

import org.kframework.attributes.Att

package object tiny {
  type Sort = kore.Sort

  type Rule = K => Set[K]

  lazy val True = new And(Set(), Att())
  lazy val False = new Or(Set(), Att())

  //  def ins[T](x: T) = { println(x); x }

  implicit class WithIns[T](x: T) {
    def ins = { println(x); x }
  }

  implicit class ToDNF(t: K) {
    def toDNF: K = t match {
      case and: And => and.children.map(_.toDNF).fold(True)({
        (or1: K, or2: K) =>
          Or(for (c1 <- AsOr(or1).children;
                  c2 <- AsOr(or2).children) yield {
            And(c1, c2)
          })
      })
      case or: Or => or.map(_.toDNF)
      case k: K => k
    }
  }

  implicit class AsAnd(thisAnd: K) {
    def children: Set[K] = thisAnd match {
      case AndChildren(thisC) => thisC
    }

    lazy val bindings = children collect {
      case b: Binding => b
    }

    lazy val binding: Map[KVar, K] = bindings map {
      case Binding(k, v, _) => (k, v)
    } toMap

    lazy val isPureSubsitution: Boolean = binding.size == children.size
  }

  implicit class AsOr(thisOr: K) {
    def |(thatOr: K) = Or(children | AsOr(thatOr).children)

    def children: Set[K] = thisOr match {
      case OrChildren(thisC) => thisC
    }

    def eliminateGroundBooleans: K = if (children.contains(True)) True else thisOr

    //      children.foldLeft(False: K) {
    //      case (_, True) => Or(True)
    //      //    case (sum, TypedKTok(Sorts.Bool, true, _)) => Or(True)
    //      case (True, _) => Or(True)
    //      case (sum: Or, False) => sum
    //      //    case (sum, TypedKTok(Sorts.Bool, false, _)) => sum
    //      case (sum: Or, p) => Or(sum.children + p)
    //    }
  }

}
