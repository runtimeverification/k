// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collections;

import org.junit.Test;

public class AndOrTreeTest {

    @Test
    public void testLeaf() {
        AndOrTree<Integer> tree1 = new AndOrTree<>(0);
        assertEquals(Collections.singletonList(Collections.singletonList(0)), tree1.sumOfProducts());
    }

    @Test
    public void testAnd() {
        AndOrTree<Integer> tree2 = new AndOrTree<>(true, new AndOrTree<>(0), new AndOrTree<>(1));
        assertEquals(Collections.singletonList(Arrays.asList(0, 1)), tree2.sumOfProducts());
        AndOrTree<Integer> tree3 = new AndOrTree<>(true, tree2, tree2);
        assertEquals(Collections.singletonList(Arrays.asList(0, 1, 0, 1)), tree3.sumOfProducts());
    }

    @Test
    public void testOr() {
        AndOrTree<Integer> tree4 = new AndOrTree<>(false, new AndOrTree<>(0), new AndOrTree<>(1));
        assertEquals(Arrays.asList(Collections.singletonList(0), Collections.singletonList(1)),
                tree4.sumOfProducts());
        AndOrTree<Integer> tree5 = new AndOrTree<>(false, new AndOrTree<>(2), new AndOrTree<>(3));
        AndOrTree<Integer> tree6 = new AndOrTree<>(false, tree4, tree5);
        assertEquals(Arrays.asList(Collections.singletonList(0), Collections.singletonList(1),
                Collections.singletonList(2), Collections.singletonList(3)), tree6.sumOfProducts());
    }

    @Test
    public void testAndInsideOr() {
        AndOrTree<Integer> tree2 = new AndOrTree<>(true, new AndOrTree<>(0), new AndOrTree<>(1));
        AndOrTree<Integer> tree7 = new AndOrTree<>(true, new AndOrTree<>(2), new AndOrTree<>(3));
        AndOrTree<Integer> tree8 = new AndOrTree<>(false, tree2, tree7);
        assertEquals(Arrays.asList(Arrays.asList(0, 1), Arrays.asList(2, 3)), tree8.sumOfProducts());
    }

    @Test
    public void testOrInsideAnd() {
        AndOrTree<Integer> tree4 = new AndOrTree<>(false, new AndOrTree<>(0), new AndOrTree<>(1));
        AndOrTree<Integer> tree8 = new AndOrTree<>(true, tree4, tree4);
        assertEquals(Arrays.asList(Arrays.asList(0, 0), Arrays.asList(0, 1), Arrays.asList(1, 0),
                Arrays.asList(1, 1)), tree8.sumOfProducts());
    }

    @Test
    public void testComplex() {
        AndOrTree<Integer> tree9 = new AndOrTree<>(true,
                new AndOrTree<>(0),
                new AndOrTree<>(true,
                        new AndOrTree<>(1),
                        new AndOrTree<>(2),
                        new AndOrTree<>(false,
                                new AndOrTree<>(true,
                                        new AndOrTree<>(3),
                                        new AndOrTree<>(4)),
                                new AndOrTree<>(5))));
        assertEquals(Arrays.asList(Arrays.asList(0, 1, 2, 3, 4), Arrays.asList(0, 1, 2, 5)), tree9.sumOfProducts());
    }

}
