package org.kframework.tiny

import org.junit.{Before, Assert}
import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.definition.{NonTerminal, Module, Production}
import org.kframework.unparser.Unparse


trait AbstractTest {

  import org.kframework.builtin.Sorts._
  import org.kframework.kore._
  import org.kframework.{kore, tiny}

  val module = Module("TEST", Set(), Set(
    Production("_andBool_", Sorts.Bool,
      Seq(NonTerminal(Sorts.Bool), NonTerminal(Sorts.Bool)), Att() + ("hook" -> "#BOOL:_andBool_")),
    Production("_orBool_", Sorts.Bool,
      Seq(NonTerminal(Sorts.Bool), NonTerminal(Sorts.Bool)), Att() + ("hook" -> "#BOOL:_orBool_")),
    Production("#KSequence", Sorts.KSeq, Seq(), Att() + "assoc"),
    Production("foo", String, Seq(), Att()),
    Production("bar", String, Seq(), Att()),
    Production("+", Int, Seq(), Att() + "assoc"),
    Production("MyBag", Sorts.K, Seq(), Att() + "assoc" + "comm")
  ), Att())

  val theory = new TheoryWithFunctions(module)

  val cons = new tiny.Constructors(module, theory)

  val X = KVar("X")
  val Y = KVar("Y")
  val Z = KVar("Z")

  def assertEquals(k1: kore.K, k2: kore.K) {
    if (k1 != k2)
      Assert.assertEquals(Unparse(k1), Unparse(k2))
  }

  def assertNotEquals(k1: kore.K, k2: kore.K): Unit = {
    if (k1 == k2)
      Assert.assertNotEquals(Unparse(k1), Unparse(k2))
  }

  @Before def clearCache: Unit = {
    theory.cache.invalidateAll()
  }
}
