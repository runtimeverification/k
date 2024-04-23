// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework;

import static org.junit.Assert.*;

import java.util.Optional;
import org.apache.commons.lang3.tuple.Pair;
import org.junit.Test;
import org.kframework.utils.errorsystem.KEMException;

public class POSetTest {
  private static final class Bar {
    private final int x;

    public Bar(int x) {
      this.x = x;
    }

    @Override
    public boolean equals(Object obj) {
      if (obj instanceof Bar b) {
        return x == b.x;
      }
      return false;
    }
  }

  private final Bar b1 = new Bar(1),
      b2 = new Bar(2),
      b3 = new Bar(3),
      b4 = new Bar(4),
      b5 = new Bar(5);

  @Test
  public void transitiveness() {
    POSet<Bar> p = new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b4, b5));

    assertTrue(p.lessThan(b1, b3));
    assertTrue(p.lessThan(b1, b2));
    assertFalse(p.greaterThan(b1, b1));
    assertFalse(p.lessThan(b1, b1));
    assertFalse(p.lessThan(b1, b4));
  }

  @Test(expected = KEMException.class)
  public void circularityTestFail() {
    new POSet<>(Pair.of(b1, b2), Pair.of(b2, b1));
  }

  @Test(expected = KEMException.class)
  public void circularityTestFailId() {
    new POSet<>(Pair.of(b1, b1));
  }

  @Test(expected = KEMException.class)
  public void circularityTestFailThree() {
    new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b3, b2));
  }

  @Test
  public void lub() {
    assertEquals(Optional.of(b2), new POSet<>(Pair.of(b1, b2)).maximum());
    assertEquals(Optional.of(b3), new POSet<>(Pair.of(b1, b3), Pair.of(b2, b3)).maximum());
    assertEquals(
        Optional.of(b4), new POSet<>(Pair.of(b1, b3), Pair.of(b2, b3), Pair.of(b3, b4)).maximum());
    assertEquals(
        Optional.empty(), new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b4, b5)).maximum());
    assertEquals(
        Optional.empty(), new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b2, b4)).maximum());
  }

  @Test
  public void glb() {
    assertEquals(Optional.of(b2), new POSet<>(Pair.of(b2, b1)).minimum());
    assertEquals(Optional.of(b3), new POSet<>(Pair.of(b3, b1), Pair.of(b3, b2)).minimum());
    assertEquals(
        Optional.of(b4), new POSet<>(Pair.of(b3, b1), Pair.of(b3, b2), Pair.of(b4, b3)).minimum());
    assertEquals(
        Optional.empty(), new POSet<>(Pair.of(b2, b1), Pair.of(b3, b2), Pair.of(b5, b4)).minimum());
    assertEquals(
        Optional.empty(), new POSet<>(Pair.of(b2, b1), Pair.of(b3, b2), Pair.of(b4, b2)).minimum());
  }

  @Test
  public void connectedComponents() {
    POSet<Bar> p = new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b4, b5));
    var components = p.connectedComponents();

    assertEquals(components.get(b1), components.get(b2));
    assertEquals(components.get(b2), components.get(b3));

    assertEquals(components.get(b4), components.get(b5));

    assertNotEquals(components.get(b1), components.get(b4));
  }

  @Test
  public void connected2() {
    POSet<Bar> p = new POSet<>(Pair.of(b1, b2), Pair.of(b4, b5), Pair.of(b2, b3), Pair.of(b3, b4));
    var components = p.connectedComponents();

    assertEquals(components.get(b1), components.get(b2));
    assertEquals(components.get(b1), components.get(b3));
    assertEquals(components.get(b1), components.get(b4));
    assertEquals(components.get(b1), components.get(b5));
  }

  @Test
  public void connected3() {
    POSet<Bar> p = new POSet<>(Pair.of(b1, b2), Pair.of(b3, b4));
    var components = p.connectedComponents();

    assertEquals(components.get(b1), components.get(b2));
    assertEquals(components.get(b3), components.get(b4));
    assertNotEquals(components.get(b1), components.get(b3));
  }

  @Test
  public void connected4() {
    POSet<Bar> p = new POSet<>(Pair.of(b1, b2), Pair.of(b2, b3), Pair.of(b3, b4), Pair.of(b3, b5));
    var components = p.connectedComponents();

    assertEquals(components.get(b1), components.get(b2));
    assertEquals(components.get(b1), components.get(b3));
    assertEquals(components.get(b1), components.get(b4));
    assertEquals(components.get(b1), components.get(b5));
  }
}
