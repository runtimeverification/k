package org.kframework.tiny


import java.util
import java.util.Optional

import org.kframework.builtin.Sorts
import org.kframework.definition.{Module, ModuleTransformer}
import org.kframework.kore.Unapply.KLabel
import org.kframework.kore.{KApply, Unapply}
import org.kframework.rewriter.SearchType
import org.kframework.{rewriter, RewriterResult, definition, kore}

import scala.collection.parallel.ParIterable

object KIndex extends (K => Option[Symbol]) {
  def apply(k: K): Option[Symbol] = k match {
    case KApp(KLabel("<k>"), c, _) =>
      val top = c.head match {
        case s: KSeq => s.children.headOption.getOrElse(KSeq())
        case x => x
      }
      SimpleIndex(top) map { s => Symbol("<k>" + s.toString) }
    case x => SimpleIndex(x)
  }
}

object SimpleIndex extends (K => Option[Symbol]) {
  def apply(k: K): Option[Symbol] = k match {
    case KRewrite(l, _, _) => apply(l)
    case KApp(l, _, _) => Some(Symbol(l.toString))
    case v => None
  }
}

class FullTinyRewriter(module: definition.Module) extends rewriter.Rewriter {
  val moduleWithoutFunctions = ModuleTransformer(m => Module(
    m.name, m.imports, m.localSentences.filter({
      case r: org.kframework.definition.Rule =>
        r.body match {
          case Unapply.KRewrite(app: KApply, _) => !module.attributesFor(app.klabel).contains("function")
          case _ => true
        }
      case _ => true
    })), "CreateModuleForFunctions").apply(module)

  val innerRewriter = new Rewriter(moduleWithoutFunctions, KIndex, new TheoryWithFunctions(module))

  def execute(k: kore.K, depth:java.util.Optional[Integer]): RewriterResult = new RewriterResult(java.util.Optional.of(-1), innerRewriter.execute(k))
  def executeAndMatch(k: kore.K, depth: Optional[Integer], rule: org.kframework.definition.Rule): (kore.K, java.util.List[java.util.Map[kore.KVariable, kore.K]]) = ???
  def search(initialConfiguration: kore.K, depth: Optional[Integer], bound: Optional[Integer], pattern: org.kframework.definition.Rule, searchType: SearchType): java.util.List[_ <: java.util.Map[_ <: kore.KVariable, _ <: kore.K]] = ???
  override def `match`(k: kore.K, rule: org.kframework.definition.Rule): java.util.List[java.util.Map[kore.KVariable, kore.K]] = ???

  override def prove(rules: util.List[definition.Rule]): util.List[kore.K] = ???
}

class Rewriter(module: definition.Module, index: K => Option[Symbol] = KIndex, theory: Theory) {

  val cons = new Constructors(module, theory)

  import cons._

  def createRule(r: definition.Rule): Rule = {
    val sideCondition = liftedSideCondition(r)

    if (r.att.contains("anywhere"))
      AnywhereRule(convert(r.body), sideCondition)
    else
      RegularRule(convert(r.body), sideCondition)
  }

  def createExecuteRule(r: definition.Rule): Rule = {
    val sideCondition = liftedSideCondition(r)

    if (r.att.contains("anywhere"))
      AnywhereRule(convert(r.body), sideCondition)
    else
      ExecuteRule(convert(r.body), sideCondition)
  }

  def liftedSideCondition(r: definition.Rule): K = {
    if (module.optionSortFor(r.requires) == Some(Sorts.Bool))
      LiftBoolToML(convert(r.requires))
    else
      convert(r.requires)
  }

  val rules = module.rules map createRule

  val indexedRules: Map[Option[Symbol], ParIterable[Rule]] = {
    module.rules
      .groupBy { r => index(convert(r.body)) }
      .map { case (k, ruleSet) =>
      (k, ruleSet
        .map(createRule)
        .seq.view.par)
    }
  }

  val executeRules = module.rules
    .map(createExecuteRule)
    .seq.view.par

  val indexedExecuteRules: Map[Option[Symbol], ParIterable[Rule]] = {
    module.rules
      .groupBy { r => index(convert(r.body)) }
      .map { case (k, ruleSet) =>
      (k, ruleSet
        .map(createExecuteRule)
        .seq.view.par)
    }
  }


  def rewriteStep(k: K): Set[K] = {
    val i = index(k)

    val prioritized = indexedRules.get(i).getOrElse({
      indexFailures += 1;
      rules
    })

    val res = prioritized
      .flatMap { r => totalTriedRules += 1; r(k) }

    res.seq.toSet
  }

  var totalTriedRules = 0
  var indexFailures = 0

  def executeStep(kk: K): Option[K] = {
    //    println("\n\n MATCHING ON: " + k)

    val k = kk.normalize

    val i = index(k)

    val prioritized = indexedExecuteRules.get(i).getOrElse({
      indexFailures += 1;
      executeRules
    })

    val res = prioritized
      .map { r =>
      totalTriedRules += 1
      val res = r(k).headOption
      res match {
        case Some(res) =>
          //          println(r + "\n" + res + "\n");
          Some(res)
        case None => None
      }
    }
      .find {
      _.isInstanceOf[Some[_]]
    }
      .getOrElse(None)
    //    println("RESULT:\n    " + res.mkString("\n    "))
    res
  }

  def execute(k: kore.K): kore.K = execute(cons.convert(k))

  def proveRule(ruleToProve: definition.Rule, allRules: java.util.List[definition.Rule]) = throw new UnsupportedOperationException

  def execute(k: K): K = {
    var steps = 0
    var time = System.nanoTime()
    var current: K = k.normalize
    var prev: K = null
    do {
      steps += 1
      if (steps % 1000 == 0) {
        println(steps +
          " runtime: " + (System.nanoTime() - time) / 1000000 +
          " cache size: " + theory.cache.size +
          " avg tried rules: " + totalTriedRules / steps +
          " index failures: " + indexFailures)
        time = System.nanoTime()
      }
      prev = current;
      current = executeStep(prev) match {
        case Some(newK) => newK
        case None => prev
      }
    } while (current != prev)
    current
  }

  def rewrite(k: kore.K)(implicit sofar: Set[kore.K] = Set()): Set[kore.K] = {
    val sofarTiny = sofar map convert

    val newKs = rewriteStep(convert(k)) &~ sofarTiny
    if (newKs.size == 0)
      sofar
    else {
      val newSoFar = sofarTiny | newKs
      newKs flatMap {
        rewrite(_)(newSoFar.asInstanceOf[Set[kore.K]])
      }
    }
  }

  def search(k: K, pattern: K)(implicit sofar: Set[K] = Set()): Either[Set[K], K] = {
    val newKs = (rewriteStep(k) &~ sofar).toStream

    newKs find {
      pattern.matcher(_).normalize == True
    } map {
      Right(_)
    } getOrElse {
      if (newKs.size == 0)
        Left(Set[K]())
      else {
        val newSoFar = sofar | newKs.toSet
        (newKs map {
          search(_, pattern)(newSoFar)
        }).fold(Left(Set[K]())) {
          case (Left(sum), Left(n)) => Left(sum | n)
          case (Left(sum), Right(k)) => Right(k)
          case (Right(k), _) => Right(k)
        }
      }
    }
  }
}
