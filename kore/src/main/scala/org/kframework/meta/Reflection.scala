package org.kframework.meta

import collection.JavaConverters._

object Reflection {
  import scala.reflect.runtime.universe._
  val m = runtimeMirror(getClass.getClassLoader)

  def getTypeTag[T: TypeTag](obj: T) = typeTag[T]

  def findObject(name: String): Any = {
    val moduleSymbol = m.staticModule(name)
    val moduleMirror = m.reflectModule(moduleSymbol)
    moduleMirror.instance
  }

  val box = Map[Class[_], Class[_]](
    Integer.TYPE -> classOf[Integer]).withDefault { x => x }

  def <=(a: Class[_], b: Class[_]): Boolean = {
    box(b).isAssignableFrom(box(a))
  }

  def <=(a: Seq[Class[_]], b: Seq[Class[_]]): Boolean = { // assuming the seqences are equal
    !(a.zip(b) exists { case (aa, bb) => ! <=(aa, bb) })
  }

  def deconstruct(o: Any): TraversableOnce[Any] = o match {
    case o: Iterable[_] => o.iterator
    case o: Product => o.productIterator
    case o: java.lang.Iterable[_] => o.asScala.iterator
    case o: Iterator[_] => o
    case _ => Seq()
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
      case tooMany => throw new AssertionError("Found too many constructors for arguments: " + (args map { _.getClass() }) + "\n The constructors are " + tooMany.mkString(" ; "))
    }
  }

  def invokeMethod(obj: Any, methodName: String, givenArgsLists: Seq[Seq[Any]]): Any = {
    val givenArgsTypes = givenArgsLists map { _ map { _.getClass().asInstanceOf[Class[Any]] } }

    val (methodSymbol, paramsListsWithDefauls) = findMethod(obj, methodName, givenArgsTypes)

    val methodMirror = mirrorForMethod(obj, methodSymbol)

    val args = completeArgsWithDefaults(paramsListsWithDefauls, givenArgsLists)

    try { methodMirror.apply(args: _*) }
    catch {
      case _: IllegalArgumentException => methodMirror.apply(args)
      case _: IndexOutOfBoundsException => methodMirror.apply(args)
    }
  }

  def mirrorForMethod(obj: Any, methodSymbol: reflect.runtime.universe.MethodSymbol) = {
    val instanceMirror = m.reflect(obj)
    instanceMirror.reflectMethod(methodSymbol)
  }

  def typesForArgs(givenArgsLists: Seq[Seq[Any]]) = {
    givenArgsLists map { _ map { _.getClass().asInstanceOf[Class[Any]] } }
  }

  def completeArgsWithDefaults(paramsListsWithDefauls: Seq[Seq[Either[Class[_], reflect.runtime.universe.MethodMirror]]], givenArgsLists: Seq[Seq[Any]]) = {
    paramsListsWithDefauls.zipAll(givenArgsLists, null, Seq()).foldLeft(Seq[Any]())({
      case (argsSoFar, (paramsWithDefaults, args)) =>
        val newArgs = paramsWithDefaults.zipAll(args, null, null) map {
          case (c: Left[_, _], givenArg) => givenArg
          case (Right(defaultArg), null) => defaultArg(argsSoFar: _*)
          case (null, arg) => arg
          case _ => throw new AssertionError("Should be unreachable: ")
        }
        argsSoFar ++ newArgs
    })
  }

  def findMethod(obj: Any, methodName: String, givenArgsLists: Seq[Seq[Class[Any]]]): (MethodSymbol, Seq[Seq[Either[Class[_], MethodMirror]]]) = {
    val instanceMirror = m.reflect(obj)

    val methodTermName = newTermName(methodName)
    val typeSignature = instanceMirror.symbol.typeSignature
    val termSymbol = typeSignature member methodTermName

    if (termSymbol == NoSymbol)
      throw new NoSuchMethodException("Could not find method: " + methodName)

    def valueFor(name: String, p: Symbol, i: Int): Option[MethodMirror] = {
      val defarg = typeSignature member newTermName(s"$name$$default$$${i + 1}")
      if (defarg != NoSymbol) {
        Some(instanceMirror reflectMethod defarg.asMethod)
      } else
        None
    }

    val methodSymbolAlternatives = termSymbol.asTerm.alternatives

    def paramTypesFor(sym: MethodSymbol) = sym.asMethod.paramLists.flatten
      .map { _.typeSignature.erasure.typeSymbol.asClass }
      .map { m.runtimeClass(_) }

    def typeszip(sym: MethodSymbol, argsLists: Seq[Seq[Either[Class[_], MethodMirror]]]) = {
      val paramTypes = paramTypesFor(sym: MethodSymbol)
      val argsTypes = argsLists.flatten map {
        case Left(c) => c
        case Right(mm) =>
          m.runtimeClass(mm.symbol.returnType.erasure)
      }
      paramTypes.zip(argsTypes)
    }

    def isVarArg(s: Symbol) = s.info.toString().contains("*")
    def isVarArgs(params: List[Symbol]) = params exists isVarArg

    val possibleMethods = methodSymbolAlternatives
      .map { _.asMethod }
      .filter { _.paramLists.size >= givenArgsLists.size }
      .filter {
        !_.paramLists.zipAll(givenArgsLists, null, Seq()).exists({
          case (params, givenArgs) =>
            params.size < givenArgs.size && !isVarArgs(params)
        })
      }
      .map { methodSymbol =>
        val paramsWithGivenArgsLists = methodSymbol.paramLists
          .zipAll(givenArgsLists, null, Seq())
          .map {
            case (params, args) =>
              val res = params.zipAll(args map { Some(_) }, null, None)
              if (isVarArgs(params)) {
                val cutPos = params indexWhere isVarArg
                res.slice(0, cutPos)
              } else
                res
          }
        val paramsWithGivenArgsAndIndex = paramsWithGivenArgsLists.foldLeft((0, List[List[((Symbol, Option[Class[Any]]), Int)]]())) {
          case ((index, newPList), pList) => (index + pList.size, newPList :+
            (pList.zipWithIndex map {
              case (v, i) => (v, i + index)
            }))
        }

        // the left of Either is a Class, the right is a default value
        val argsLists = paramsWithGivenArgsAndIndex._2 map {
          case args =>
            val argsWithDefaults = args
              .map {
                case ((sym, Some(v)), _) => Some(Left(v))
                case ((sym, None), index) =>
                  valueFor(methodName, sym, index) map { Right(_) }
              }
            if (argsWithDefaults.contains(None))
              None
            else {
              Some((argsWithDefaults map { _.get }): List[Either[Class[_], MethodMirror]])
            }
        }
        (methodSymbol, argsLists)
      }
      .collect {
        case (sym, argsLists) if !argsLists.contains(None) =>
          (sym, argsLists collect { case Some(x) => x })
      }
      .filter {
        case (sym, argsLists) =>
          !(typeszip(sym, argsLists) exists {
            case (paramType, argType) => ! <=(argType, paramType)
          })
      }
    val eliminatedSubsorted = possibleMethods.filter {
      case (sym, argsLists) =>
        val otherMethods = possibleMethods map { _._1 } filter { _ != sym } map paramTypesFor
        !(otherMethods exists { other => <=(other, paramTypesFor(sym)) })
    }

    eliminatedSubsorted match {
      case List() => throw new IllegalArgumentException(methodName + " " + givenArgsLists)
      case List(x) => x
      case x => (possibleMethods find {
        case (sym, argsLists) =>
          !(typeszip(sym, argsLists) exists {
            case (a, b) => box(a) != box(b)
          })
      }).getOrElse({
        throw new RuntimeException("Could not find an exact match for method " + methodName + " with arg types " + givenArgsLists)
      })
    }
  }
}
