// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import static org.junit.Assert.*;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.DisjunctiveFormula;

import org.junit.Test;

public class ConjunctionDisjunctionTest {

    @Test
    public void testSimple() {
        ConjunctiveFormula c0 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(0));
        ConjunctiveFormula c1 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(1));
        ConjunctiveFormula c2 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(2));
        DisjunctiveFormula d0 = new DisjunctiveFormula(ImmutableList.of(c1, c2), null);
        DisjunctiveFormula d1 = new DisjunctiveFormula(
                ImmutableList.of(c0.add(c1), c0.add(c2)),
                null);
        assertEquals(c0.add(d0).getDisjunctiveNormalForm(), d1);
    }

    @Test
    public void testComplex() {
        ConjunctiveFormula c0 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(0));
        ConjunctiveFormula c1 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(1));
        ConjunctiveFormula c2 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(2));
        ConjunctiveFormula c3 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(3));
        DisjunctiveFormula d0 = new DisjunctiveFormula(ImmutableList.of(c0, c1), null);
        DisjunctiveFormula d1 = new DisjunctiveFormula(ImmutableList.of(c2, c3), null);
        ConjunctiveFormula c4 = ConjunctiveFormula.of((GlobalContext) null).add(d0).add(d1);
        DisjunctiveFormula d2 = new DisjunctiveFormula(
                ImmutableList.of(c0.add(c2), c0.add(c3), c1.add(c2), c1.add(c3)),
                null);
        assertEquals(c4.getDisjunctiveNormalForm(), d2);

        ConjunctiveFormula c5 = ConjunctiveFormula.of((GlobalContext) null)
                .add(IntToken.of(0), IntToken.of(5));
        DisjunctiveFormula d3 = new DisjunctiveFormula(
                ImmutableList.of(
                        c5.add(c0).add(c2),
                        c5.add(c0).add(c3),
                        c5.add(c1).add(c2),
                        c5.add(c1).add(c3)),
                null);
        assertEquals(c5.add(c4).getDisjunctiveNormalForm(), d3);
    }

}
