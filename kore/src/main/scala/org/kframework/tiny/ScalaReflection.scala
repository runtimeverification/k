package org.kframework.tiny

object Reflection {
  import scala.reflect.runtime.universe._
  import scala.reflect.ClassTag
  val m = runtimeMirror(getClass.getClassLoader)

  def getTypeTag[T: TypeTag](obj: T) = typeTag[T]

  def findObject(name: String): Any = {
    val moduleSymbol = m.staticModule(name)
    val moduleMirror = m.reflectModule(moduleSymbol)
    moduleMirror.instance
  }

  def invokeMethod(obj: Any, methodName: String, givenArgsLists: Seq[Seq[Any]]) = {
    val moduleInstanceMirror = m.reflect(obj)

    val applyTermName = newTermName(methodName)
    val moduleTypeSignature = moduleInstanceMirror.symbol.typeSignature
    val applySymbol = moduleTypeSignature member applyTermName

    val applyMethodSymbolAlternatives = applySymbol.asTerm.alternatives

    val applyMethodSymbol = (if (applyMethodSymbolAlternatives.size == 1)
      applyMethodSymbolAlternatives.head
    else {
      applyMethodSymbolAlternatives.head // TODO: fix this for methods with true overloading
    }).asMethod

    def valueFor(name: String, p: Symbol, i: Int, argsSoFar: List[Any]): Any = {
      val defarg = moduleTypeSignature member newTermName(s"$name$$default$$${i + 1}")
      if (defarg != NoSymbol)
        (moduleInstanceMirror reflectMethod defarg.asMethod)(argsSoFar: _*)
      else
        throw new IllegalArgumentException(name + " " + p + " " + i + defarg.toString)
    }
    val paramsWithGivenArgsLists = applyMethodSymbol.paramLists
      .zipAll(givenArgsLists, null, Seq())
      .map { case (params, args) => params.zipAll(args map { Option(_) }, null, None) }

    val paramsWithGivenArgsAndIndex = paramsWithGivenArgsLists.foldLeft((0, List[List[((Symbol, Option[Any]), Int)]]())) {
      case ((index, newPList), pList) => (index + pList.size, newPList :+
        (pList.zipWithIndex map {
          case (v, i) => (v, i + index)
        }))
    }

    val args = paramsWithGivenArgsAndIndex._2.foldLeft(List[Any]()) {
      case (argsSoFar, args) =>
        val argsWithDefaults = args map {
          case ((_, Some(v)), _) => v
          case x @ ((sym, None), index) => valueFor(methodName, sym, index, argsSoFar)
        }
        argsSoFar ++ argsWithDefaults
    }

    val applyMethodMirror = moduleInstanceMirror.reflectMethod(applyMethodSymbol)

    applyMethodMirror.apply(args: _*)
  }
}
