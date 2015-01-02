// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework;

import java.util.stream.Stream;

import org.junit.Test;

import scala.collection.immutable.List;
import scala.collection.immutable.Set;
import static org.kframework.Collections.*;
import static org.junit.Assert.*;

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

    @Test
    public void testAssociativeList() {

        Stream<Integer> s = stream(List(1, 2, 3));

        // splitting 3 into a list
        Stream<Object> l = s.map(x -> {
            if (x == 3)
                return List(1, 2);
            else
                return x;
        });

        // and now... converting it to an Sssociative List
        List<Object> collectedList = l.collect(toAssociativeList());

        // check out the result
        assertEquals(List(1, 2, 1, 2), collectedList);

        // yes, the types are not perfect, some casting is needed,
        // but you cannot really ask too much from Java
    }

    @Test
    public void moreNestingJustToBeSure() {

        Stream<Object> s = stream(List(1, List(2, List(3, 4)), List(5)));

        // and now... converting it to an assoc List
        List<Object> collectedList = s.collect(toAssociativeList());

        // check out the result
        assertEquals(List(1, 2, 3, 4, 5), collectedList);
    }

    @Test
    public void testAssociativeSet() {

        Stream<Integer> s = stream(Set(1, 2, 3));

        // usual Java 8 manipulation
        Stream<Object> l = s.map(x -> Set(x / 2));

        // and back to an *assoc* Set
        Set<Object> collectedList = l.collect(toAssociativeSet());

        // which has the expected value
        assertEquals(Set(0, 1), collectedList);
    }
}
