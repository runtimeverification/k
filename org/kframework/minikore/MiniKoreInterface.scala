package org.kframework.minikore

/**
  * Created by daejunpark on 1/26/17.
  */
object MiniKoreInterface {

  trait Pattern

  trait And extends Pattern {
    def p: Pattern
    def q: Pattern
  }

  //trait PatternConstructor

  trait AndConstructor /*extends PatternConstructor*/ {
    def apply(p: Pattern, q: Pattern): Pattern
  }

}
