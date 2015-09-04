package org.kframework

import org.kframework.attributes.Att

package object tiny {
  type Sort = kore.Sort

  lazy val True = new And(Set(), Att())
  lazy val False = new Or(Set(), Att())

  def ins[T](x: T) = { println(x); x }

  implicit class WithIns[T](x: T) {
    def ins = { println(x); x }
  }

  implicit class HasDNF(val t: K) extends AnyVal {
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

  implicit class AsAnd(val thisAnd: K) extends AnyVal {
    def children: Set[K] = thisAnd match {
      case and: And => and.children
      case k: K => Set(k)
    }

    def binding: Map[KVar, K] = thisAnd match {
      case and: And => and.binding
      case k: Binding => Map(k.variable -> k.value)
      case _ => Map()
    }

    def isPureSubsitution: Boolean = binding.size == children.size

    def isSolved = isPureSubsitution && !children.exists(!_.isGround)
  }

  implicit class AsOr(val thisOr: K) extends AnyVal {
    def |(thatOr: K) = Or(children | AsOr(thatOr).children)

    def children: Set[K] = thisOr match {
      case or: Or => or.children
      case k: K => Set(k)
    }
  }

}
