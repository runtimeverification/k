package org.kframework.meta

abstract class AbstractReflectiveVisitor {
  import scala.reflect.runtime.universe.MethodMirror
  val cache = collection.mutable.Map[Class[_], MethodMirror]()
  //  val cache = collection.mutable.Map[Class[_], Method]()

  def apply(o: Any) {
    val methodMirror = cache.getOrElseUpdate(o.getClass, {
      val types = Reflection.typesForArgs(Seq(Seq(o)))
      val (methodSymbol, _) = Reflection.findMethod(this, "visit", types)
      Reflection.mirrorForMethod(this, methodSymbol)
    })
    methodMirror(o)
    Reflection.deconstruct(o) foreach apply
  }
  def visit(x: AnyRef) {}
}
