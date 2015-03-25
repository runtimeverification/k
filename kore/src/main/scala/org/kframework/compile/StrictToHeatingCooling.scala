package org.kframework.compile

import org.kframework.definition._
import org.kframework.kore.K
import org.kframework.kore.KORE._

class ModuleTransformation(f: Module => Module) extends (Module => Module) {
  val memoization = collection.mutable.HashMap[Module, Module]()

  override def apply(input: Module): Module = {
    memoization.getOrElseUpdate(input, f(Module(input.name, input.imports map this, input.localSentences, input.att)))
  }
}

object StrictToHeatingCooling extends ModuleTransformation({m: Module =>
  val True = KLabel("_andBool_")()
  val False = KLabel("_orBool_")()
  val hole = KLabel("[]")()

  // TODO: remove hack once configuration concretization is working
  def concretize(k: K) = KLabel("<top>")(KLabel("<k>")(k), KVariable("SC"))

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
      val restVar = KVariable("R")
      Set(
        Rule(
          concretize(KSequence(KRewrite(cooled, heated(i)), restVar)),
          KLabel("notBool_")(isKResult(i)),
          False, Att() + "heat"),
        Rule(
          concretize(KSequence(KRewrite(heated(i), cooled), restVar)),
          isKResult(i),
          False, Att() + "cool")
      )
    }
  }

  Module(m.name, m.imports, m.sentences ++ heatingCoolingRules, m.att)
})
