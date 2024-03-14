// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework

import java.util.Optional
import org.junit.Assert._
import org.junit.Test
import org.kframework.utils.errorsystem.KEMException

class POSetTest {
  case class Bar(x: Int)

  import POSet._

  val b1 = Bar(1); val b2 = Bar(2); val b3 = Bar(3); val b4 = Bar(4); val b5 = Bar(5)

  @Test def transitiveness() {
    val p = new POSet(b1 -> b2, b2 -> b3, b4 -> b5)

    assertTrue(p.lessThan(b1, b3))
    assertTrue(p.lessThan(b1, b2))
    assertFalse(p.greaterThan(b1, b1))
    assertFalse(p.lessThan(b1, b1))
    assertFalse(p.lessThan(b1, b4))
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFail() {
    new POSet(b1 -> b2, b2 -> b1)
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFailId() {
    new POSet(b1 -> b1)
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFailThree() {
    new POSet(b1 -> b2, b2 -> b3, b3 -> b2)
  }

  @Test def lub() {
    assertEquals(Optional.of(b2), new POSet(b1 -> b2).maximum)
    assertEquals(Optional.of(b3), new POSet(b1 -> b3, b2 -> b3).maximum)
    assertEquals(Optional.of(b4), new POSet(b1 -> b3, b2 -> b3, b3 -> b4).maximum)
    assertEquals(Optional.empty(), new POSet(b1 -> b2, b2 -> b3, b4 -> b5).maximum)
    assertEquals(Optional.empty(), new POSet(b1 -> b2, b2 -> b3, b2 -> b4).maximum)
  }

  @Test def glb() {
    assertEquals(Optional.of(b2), new POSet(b2 -> b1).minimum)
    assertEquals(Optional.of(b3), new POSet(b3 -> b1, b3 -> b2).minimum)
    assertEquals(Optional.of(b4), new POSet(b3 -> b1, b3 -> b2, b4 -> b3).minimum)
    assertEquals(Optional.empty(), new POSet(b2 -> b1, b3 -> b2, b5 -> b4).minimum)
    assertEquals(Optional.empty(), new POSet(b2 -> b1, b3 -> b2, b4 -> b2).minimum)
  }
}
