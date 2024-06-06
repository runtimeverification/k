// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework;

import static org.junit.Assert.*;
import static org.kframework.Collections.*;
import static org.kframework.Collections.List;

import java.util.stream.Stream;
import org.junit.Test;
import scala.collection.Set;
import scala.collection.immutable.List;

public class CollectionsTest {
  @Test
  public void testList() {
    // creating a List
    List<Integer> aList = List(1, 2, 3);

    // getting a Stream from a list
    Stream<Integer> s = stream(aList);

    // usual Java 8 manipulation
    Stream<String> l = s.map(x -> x.toString());

    // and back to an immutable List
    List<String> collectedList = l.collect(toList());

    // which has the expected value
    assertEquals(List("1", "2", "3"), collectedList);
  }

  @Test
  public void testSet() {
    // creating a Set
    Set<Integer> aList = Set(1, 2, 3);

    // getting a Stream from a Set
    Stream<Integer> s = stream(aList);

    // usual Java 8 manipulation
    Stream<Integer> l = s.map(x -> x / 2);

    // and back to an immutable Set
    Set<Integer> collectedList = l.collect(toSet());

    // which has the expected value
    assertEquals(Set(0, 1), collectedList);
  }
}
