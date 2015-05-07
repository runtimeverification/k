package org.kframework.compile

import org.kframework.definition._
import org.kframework.kore.KORE._

object StrictToHeatingCooling extends ModuleTransformer({m: Module =>
  val True = KToken(Sort("Bool"), "true")
  val hole = KLabel("[]")()

  def makeVar(pos: Int) = KVariable("A" + (pos + 1))

  val heatingCoolingRules = m.productions
    .filter { _.att.contains("strict") }
    .flatMap {p: Production =>

    val klabel = p.klabel.get
    val nonTerminals = p.items.collect { case i: NonTerminal => i }
    val vars = (0 until nonTerminals.size) map makeVar toList

    val cooled = klabel(vars: _*) // e.g., A + B

    def heated(position: Int) = KSequence(vars(position), klabel(vars.updated(position, hole): _*)) // e.g., A ~> A + B

    val strictIn = p.att.get[String]("strict")
      .map {valueString =>
      if (valueString.trim == "")
        0 until nonTerminals.size toList
      else
        valueString.split(",").map { _.trim.toInt - 1 }.toList
    }
      .getOrElse(0 until nonTerminals.size toList)

    def isKResult(position: Int) = KLabel("isKResult")(vars(position))

    nonTerminals
      .zipWithIndex
      .map(_._2)
      .filter { strictIn.contains(_) }
      .flatMap {i: Int =>
      Set(
        Rule(
          KSequence(KRewrite(cooled, heated(i))),
          KLabel("notBool_")(isKResult(i)),
          True, Att() + "heat"),
        Rule(
          KSequence(KRewrite(heated(i), cooled)),
          isKResult(i),
          True, Att() + "cool")
      )
    }
  }

  Module(m.name, m.imports, m.localSentences ++ heatingCoolingRules, m.att)
}, "resolving strict attribute") {
  def self = this
}
