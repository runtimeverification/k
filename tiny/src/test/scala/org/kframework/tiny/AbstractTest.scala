package org.kframework.tiny

import org.junit.Assert
import org.kframework.attributes.Att
import org.kframework.definition.{Module, Production}
import org.kframework.kore.{ADT, Unparse}


trait AbstractTest {

  import org.kframework.tiny.Builtins._

  val cons = new Constructors(Module("TEST", Set(), Set(
    Production(ADT.KLabel("foo"), String, Seq(), Att()),
    Production(ADT.KLabel("bar"), String, Seq(), Att()),
    Production(ADT.KLabel("+"), String, Seq(), Att() + "assoc")
  ), Att()))

  val X = KVar("X")
  val Y = KVar("Y")

  def assertEquals(k1: K, k2: K) {
    if (k1 != k2)
      Assert.assertEquals(Unparse(k1), Unparse(k2))
  }

  def assertNotEquals(k1: K, k2: K): Unit = {
    if (k1 == k2)
      Assert.assertNotEquals(Unparse(k1), Unparse(k2))
  }
}
