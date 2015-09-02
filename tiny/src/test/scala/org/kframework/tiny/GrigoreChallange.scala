package org.kframework.tiny

import org.junit.Assert._
import org.junit.{Ignore, Test}
import org.kframework.attributes.Att
import org.kframework.definition._


class GrigoreChallange {

  //  mod T is
  //  including RAT .
  //  sort MSet .
  //  subsort Rat < MSet .
  //  op _,_ : MSet MSet -> MSet [assoc comm] .
  //  vars A B : Rat .
  //  rl A,B => A * B .
  //    rl A,B => A - B .
  //    rl A,B => A + B .
  //    rl A,B => A / B .
  //    endm
  //
  //  search 5,5,7,4 =>* 24 .
  //  show path 634 .

  import org.kframework.builtin.Sorts._

  val X = KVar("X")
  val Y = KVar("Y")

  val boolPair = Seq(NonTerminal(Bool), NonTerminal(Bool))

  //  val logicModule = Module("BOOLEAN-LOGIC", Set(), Set(
  //    Production("_andBool_", Bool, boolPair, Att() + ("hook" -> "#BOOL:_andBool_")),
  //    Production("_orBool_", Sorts.Bool, boolPair, Att() + ("hook" -> "#BOOL:_orBool_"))))

  val intPair = Seq(NonTerminal(Int), NonTerminal(Int))

  val syntaxModule = Module("T-SYNTAX", Set(), Set(
    Production("+", Int, intPair, Att() + ("hook" -> "#INT:_+Int_")),
    Production("-", Int, intPair, Att() + ("hook" -> "#INT:_-Int_")),
    Production("/", Int, intPair, Att() + ("hook" -> "#INT:_/Int_")),
    Production("*", Int, intPair, Att() + ("hook" -> "#INT:_*Int_")),
    Production("~", K, intPair, Att() + "assoc" + "comm")
  ), Att())

  val cons = new Constructors(syntaxModule, FreeTheory(syntaxModule))

  import cons._

  val R = KVar("R")

  val argsAreInts = And(LiftBoolToMLLabel('isInt(X)), LiftBoolToMLLabel('isInt(Y)))

  val completeModule = Module("T", Set(syntaxModule), Set(
    Rule(X ~ Y ~ R ==> (X + Y) ~ R, argsAreInts, False),
    Rule(X ~ Y ~ R ==> (X - Y) ~ R, argsAreInts, False),
    Rule(X ~ Y ~ R ==> (X / Y) ~ R, argsAreInts, False),
    Rule(X ~ Y ~ R ==> (X * Y) ~ R, argsAreInts, False)
  ))

  val rewriter = new Rewriter(completeModule, SimpleIndex, new TheoryWithFunctions(completeModule))

  @Test @Ignore
  def shortTest {
    val res = rewriter.rewrite((5: K) ~ 5 ~ 7)
    println(res.mkString("\n"))
    println(res.size + " states.")
  }

  @Test @Ignore
  def shortTestWithSearch {
    assertEquals(Right(0: K), rewriter.search((5: K) ~ 5 ~ 7, 0))
  }

  val completeModuleWithAnywhere = Module("T-ANYWHERE", Set(syntaxModule), Set(
    Rule(X ~ Y ==> (X + Y), argsAreInts, False, cons.Att() + "anywhere"),
    Rule(X ~ Y ==> (X - Y), argsAreInts, False, cons.Att() + "anywhere"),
    Rule(X ~ Y ==> (X / Y), argsAreInts, False, cons.Att() + "anywhere"),
    Rule(X ~ Y ==> (X * Y), argsAreInts, False, cons.Att() + "anywhere")
  ))

  val rewriterWithAnywhere = new Rewriter(completeModuleWithAnywhere, SimpleIndex, new TheoryWithFunctions(completeModuleWithAnywhere))

  @Test @Ignore
  def shortTestWithAnywhere {
    val res = rewriterWithAnywhere.rewrite((5: K) ~ 5 ~ 7)
    println(res.mkString("\n"))
    println(res.size + " states.")
  }

  @Test @Ignore
  def shortTestWithSearchAnywhere {
    assertEquals(Right(0: K), rewriterWithAnywhere.search((5: K) ~ 5 ~ 7, 0))
  }
}
