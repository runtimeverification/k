package org.kframework.tiny

import scala.reflect.ManifestFactory

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

  def isSubclassOf(a: Class[_], b: Class[_]) = {
    !b.isAssignableFrom(a)
  }

  def construct(className: String, args: Seq[Any]) = {
    println(Class.forName(className).getConstructors map { _.getParameterTypes.mkString(",") } mkString "\n")
    println(args map { _.getClass })

    val workingConstructors = Class.forName(className).getConstructors filter {
      case c =>
        c.getParameterCount == args.size
      //        should also check for types but the code below fails due to primitive types
      //        too lazy to build the mapping now
      //        &&
      //          !(c.getParameterTypes.zip(args) exists {
      //            case (param, arg) =>
      //              isSubclassOf(arg.getClass, param)
      //          })
    }

    workingConstructors.toList match {
      case List() => throw new AssertionError("Could not find a constructor for arguments: " + (args map { _.getClass() }))
      case c :: rest => c.newInstance(args.asInstanceOf[Seq[AnyRef]]: _*) // TODO: fix this, taking the first constructor now
      //      case tooMany => throw new AssertionError("Found too many constructors for arguments: " + (args map { _.getClass() }) + "\n The constructors are " + tooMany.mkString(" ; "))
    }
  }

  def invokeMethod(obj: Any, methodName: String, givenArgsLists: Seq[Seq[Any]]) = {
    val instanceMirror = m.reflect(obj)

    val methodTermName = newTermName(methodName)
    val typeSignature = instanceMirror.symbol.typeSignature
    val termSymbol = typeSignature member methodTermName

    val methodSymbolAlternatives = termSymbol.asTerm.alternatives

    val methodSymbol = (if (methodSymbolAlternatives.size == 1)
      methodSymbolAlternatives.head
    else {
      methodSymbolAlternatives.head // TODO: fix this for methods with true overloading
    }).asMethod

    def valueFor(name: String, p: Symbol, i: Int, argsSoFar: List[Any]): Any = {
      val defarg = typeSignature member newTermName(s"$name$$default$$${i + 1}")
      if (defarg != NoSymbol)
        (instanceMirror reflectMethod defarg.asMethod)(argsSoFar: _*)
      else
        throw new IllegalArgumentException(name + " " + p + " " + i + defarg.toString)
    }
    val paramsWithGivenArgsLists = methodSymbol.paramLists
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

    val methodMirror = instanceMirror.reflectMethod(methodSymbol)

    methodMirror.apply(args: _*)
  }
}
