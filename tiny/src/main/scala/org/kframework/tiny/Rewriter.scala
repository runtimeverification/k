package org.kframework.tiny


import org.kframework.definition
import org.kframework.kore.Unapply.KLabel
import org.kframework.kore

import scala.collection.parallel.ParIterable

object KIndex extends (K => Option[String]) {
  def apply(k: K): Option[String] = k match {
    case KApp(KLabel("<k>"), c, _) =>
      val top = c.head match {
        case s: KSeq => s.children.headOption.getOrElse(KSeq())
        case x => x
      }
      SimpleIndex(top)
    case KApp(_, l, _) =>
      l.toStream map KIndex collectFirst {
        case Some(s) => s
      }
    case _ => None
  }
}

object SimpleIndex extends (K => Option[String]) {
  def apply(k: K) = k match {
    case KApp(l, _, _) => Some(l.toString)
    case v => Some("")
  }
}

class Rewriter(module: definition.Module, index: K => Option[String] = KIndex) {
  def this(module: definition.Module) = this(module, KIndex)

  val cons = new Constructors(module)

  import cons._

  def createRule(r: definition.Rule): Rule = {
    if (r.att.contains("anywhere"))
      AnywhereRule(convert(r.body), convert(r.requires))
    else
      RegularRule(convert(r.body), convert(r.requires))
  }

  val rules = module.rules map createRule

  val indexedRules: Map[String, ParIterable[Rule]] = {
    module.rules
      .groupBy { r => index(convert(r.body)).getOrElse("NOINDEX") }
      .map { case (k, ruleSet) =>
      (k, ruleSet
        .map(createRule)
        .seq.view.par)
    }
  }

  val executeRules = module.rules
    .map { r => ExecuteRule(convert(r.body), convert(r.requires)) }
    .seq.view.par

  val indexedExecuteRules: Map[String, ParIterable[Rule]] = {
    module.rules
      .groupBy { r => index(convert(r.body)).getOrElse("NOINDEX") }
      .map { case (k, ruleSet) =>
      (k, ruleSet
        .map { r => ExecuteRule(convert(r.body), convert(r.requires)) }
        .seq.view.par)
    }
  }


  def rewriteStep(k: K): Set[K] = {
    val i = index(k).get

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

  def executeStep(k: K): Option[K] = {
//    println("\n\n MATCHING ON: " + k)

    val i = index(k).get

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
      .find {_.isInstanceOf[Some[_]]}
      .getOrElse(None)
//    println("RESULT:\n    " + res.mkString("\n    "))
    res
  }

  def execute(k: kore.K): kore.K = execute(cons.convert(k))

  def execute(k: K): K = {
    var steps = 0
    var time = System.nanoTime()
    var current: K = k
    var prev: K = null
    do {
      steps += 1
      if (steps % 1000 == 0) {
        println(steps +
          " runtime: " + (System.nanoTime() - time) / 1000000 +
          " cache size: " + NormalizationCaching.cache.size +
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
    println(steps)
    current
  }

  def rewrite(k: K)(implicit sofar: Set[K] = Set()): Set[K] = {
    val newKs = rewriteStep(k) &~ sofar
    if (newKs.size == 0)
      sofar
    else {
      val newSoFar = sofar | newKs
      newKs flatMap {
        rewrite(_)(newSoFar)
      }
    }
  }

  def search(k: K, pattern: K)(implicit sofar: Set[K] = Set()): Either[Set[K], K] = {
    val newKs = (rewriteStep(k) &~ sofar).toStream

    newKs find {pattern.matcher(_).normalize == True} map {Right(_)} getOrElse {
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
