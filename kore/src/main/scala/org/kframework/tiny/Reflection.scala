package org.kframework.tiny

import scala.reflect.ManifestFactory
import collection.JavaConverters._

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

  val unbox = Map[Class[_], Class[_]](
    classOf[Integer] -> Integer.TYPE).withDefault { x => x }

  def <(a: Class[_], b: Class[_]) = {
    unbox(b).isAssignableFrom(unbox(a))
  }

  def deconstruct(o: Any): TraversableOnce[Any] = o match {
    case o: Iterable[_] => o.iterator
    case o: Product => o.productIterator
    case o: java.lang.Iterable[_] => o.asScala.iterator
    case o: Iterator[_] => o
  }

  def construct(className: String, args: Seq[Any]) = {
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

    def valueFor(name: String, p: Symbol, i: Int, argsSoFar: List[Any]): Option[Any] = {
      val defarg = typeSignature member newTermName(s"$name$$default$$${i + 1}")
      if (defarg != NoSymbol) {
        Some((instanceMirror reflectMethod defarg.asMethod)(argsSoFar: _*))
      } else
        None
      //        throw new IllegalArgumentException(name + " " + p + " " + i + defarg.toString)
    }

    val methodSymbolAlternatives = termSymbol.asTerm.alternatives

    val symbolsWithArgs = methodSymbolAlternatives
      .map { _.asMethod }
      .filter { _.paramLists.size >= givenArgsLists.size }
      .filter {
        !_.paramLists.zipAll(givenArgsLists, null, Seq()).exists({
          case (params, givenArgs) => params.size < givenArgs.size
        })
      }
      .map { methodSymbol =>
        val paramsWithGivenArgsLists = methodSymbol.paramLists
          .zipAll(givenArgsLists, null, Seq())
          .map { case (params, args) => params.zipAll(args map { Option(_) }, null, None) }

        val paramsWithGivenArgsAndIndex = paramsWithGivenArgsLists.foldLeft((0, List[List[((Symbol, Option[Any]), Int)]]())) {
          case ((index, newPList), pList) => (index + pList.size, newPList :+
            (pList.zipWithIndex map {
              case (v, i) => (v, i + index)
            }))
        }

        val args = paramsWithGivenArgsAndIndex._2.foldLeft(Option(List[Any]())) {
          case (Some(argsSoFar), args) =>
            val argsWithDefaults = args
              .map {
                case ((sym, Some(v)), _) => Some(v)
                case x @ ((sym, None), index) => valueFor(methodName, sym, index, argsSoFar)
              }
            if (argsWithDefaults.contains(None))
              None
            else
              Some(argsSoFar ++ (argsWithDefaults map { _.get }))

          case (None, args) => None
        }
        (methodSymbol, args)
      }
      .collect {
        case (sym, Some(args)) => (sym, args)
      }
      .filter {
        case (sym, args) =>
          val paramTypes = sym.asMethod.paramLists.flatten
            .map { _.typeSignature.erasure.typeSymbol.asClass }
            .map { m.runtimeClass(_) }
          val argsTypes = args map { _.getClass }
          !(paramTypes.zip(argsTypes) exists {
            case (paramType, argType) => ! <(argType, paramType)
          })
      }

    val (methodSymbol, args) = symbolsWithArgs.head

    val methodMirror = instanceMirror.reflectMethod(methodSymbol)

    methodMirror.apply(args: _*)
  }
}
