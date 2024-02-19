// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework

import org.junit.Assert._
import org.junit.Test
import org.kframework.utils.errorsystem.KEMException

class POSetTest {
  case class Bar(x: Int)

  import POSet._

  val b1 = Bar(1); val b2 = Bar(2); val b3 = Bar(3); val b4 = Bar(4); val b5 = Bar(5)

  @Test def transitiveness() {
    implicit val p = POSet(b1 -> b2, b2 -> b3, b4 -> b5)

    assertTrue(b1 < b3)
    assertTrue(b1 < b2)
    assertFalse(b1 > b1)
    assertFalse(b1 < b1)
    assertFalse(b1 < b4)
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFail() {
    POSet(b1 -> b2, b2 -> b1)
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFailId() {
    POSet(b1 -> b1)
  }

  @Test(expected = classOf[KEMException])
  def circularityTestFailThree() {
    POSet(b1 -> b2, b2 -> b3, b3 -> b2)
  }

  @Test def lub() {
    assertEquals(Some(b2), POSet(b1 -> b2).maximum)
    assertEquals(Some(b3), POSet(b1 -> b3, b2 -> b3).maximum)
    assertEquals(Some(b4), POSet(b1 -> b3, b2 -> b3, b3 -> b4).maximum)
    assertEquals(None, POSet(b1 -> b2, b2 -> b3, b4 -> b5).maximum)
    assertEquals(None, POSet(b1 -> b2, b2 -> b3, b2 -> b4).maximum)
  }

  @Test def glb() {
    assertEquals(Some(b2), POSet(b2 -> b1).minimum)
    assertEquals(Some(b3), POSet(b3 -> b1, b3 -> b2).minimum)
    assertEquals(Some(b4), POSet(b3 -> b1, b3 -> b2, b4 -> b3).minimum)
    assertEquals(None, POSet(b2 -> b1, b3 -> b2, b5 -> b4).minimum)
    assertEquals(None, POSet(b2 -> b1, b3 -> b2, b4 -> b2).minimum)
  }
}
