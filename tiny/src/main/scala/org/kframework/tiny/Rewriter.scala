package org.kframework.tiny


import org.kframework.definition
import org.kframework.kore.Unapply.KLabel

class Rewriter(module: definition.Module) extends org.kframework.Rewriter {
  val cons = new Constructors(module)

  import cons._

  val rules = module.rules map { r => Rule(convert(r.body), convert(r.requires)) }

  val executeRules = module.rules
    .map { r => ExecuteRule(convert(r.body), convert(r.requires)) }
    .toStream

  val indexedRules: Map[String, Set[K => Option[K]]] = module.rules
    .groupBy { r => index(convert(r.body)).get }
    .mapValues { ruleSet =>
    ruleSet map { r => ExecuteRule(convert(r.body), convert(r.requires)) }
  }

  def index(k: K): Option[String] = k match {
    case KApp(KLabel("'<k>"), c, _) =>
      val top = c.head match {
        case s: KSeq => s.children.headOption.getOrElse(KSeq())
        case x => x
      }
      top match {
        case KApp(l, _, _) => Some(l.toString)
        case x => Some("foo")
      }
    case KApp(_, l, _) =>
      l.toStream map index collectFirst { case Some(s) => s }
    case _ => None
  }

  def rewriteStep(k: K): Set[K] = {
    //    println("\n\n MATCHING ON: " + k.normalize)

    val res = rules flatMap { r => r(k) }
    //    println("RESULTS:\n    " + res.mkString("\n    "))
    res
  }

  var totalTriedRules = 0

  def executeStep(k: K): Option[K] = {
    //    println("\n\n MATCHING ON: " + k)

    val i = index(k).get

    val prioritized = indexedRules.get(i).getOrElse(executeRules)

    val res = prioritized
      .map { r => totalTriedRules += 1; r(k) }
      .collectFirst { case Some(x) => x }
    //    println("RESULT:\n    " + res.mkString("\n    "))
    res
  }

  def execute(k: K): K = {
    var steps = 0
    var time = System.nanoTime()
    var current: K = k
    var prev: K = null
    do {
      steps += 1
      if (steps % 100 == 0) {
        println(steps +
          " runtime: " + (System.nanoTime() - time) / 1000000 +
          " cache size: " + NormalizationCaching.cache.size +
          " avg tried rules: " + totalTriedRules / steps)
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
      sofar | (newKs flatMap { rewrite(_)(sofar | newKs) })
    }
  }
}
