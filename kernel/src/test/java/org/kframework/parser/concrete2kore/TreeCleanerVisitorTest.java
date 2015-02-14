// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.concrete2kore;

import org.junit.Test;
import org.kframework.kore.outer.SyntaxProduction;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.ParseFailedExceptionSet;

import java.util.Arrays;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.fail;
import static org.kframework.Collections.Seq;
import static org.kframework.kore.Constructors.Sort;
import static org.kframework.kore.outer.Constructors.NonTerminal;
import static org.kframework.kore.outer.Constructors.RegexTerminal;
import static org.kframework.kore.outer.Constructors.SyntaxProduction;

public class TreeCleanerVisitorTest {

    TreeCleanerVisitor treeCleanerVisitor = new TreeCleanerVisitor();
    SyntaxProduction fooProduction = SyntaxProduction(Sort("Foo"), Seq(RegexTerminal("foo|bar")));
    Constant foo = Constant.apply("foo", fooProduction, Optional.empty());
    Constant bar = Constant.apply("bar", fooProduction, Optional.empty());

    SyntaxProduction noKLabelProduction = SyntaxProduction(Sort("NoKLabelProd"), Seq(NonTerminal(Sort("Foo")), NonTerminal(Sort("Foo"))));

    @Test
    public void testConstant() throws Exception {
        assertCleanup(foo, foo);
    }

    @Test
    public void testAmb() throws Exception {
        assertCleanup(Ambiguity.apply(foo), foo);
    }

    @Test
    public void testAmb2() throws Exception {
        Ambiguity two = Ambiguity.apply(foo, bar);
        assertCleanup(two, two);
    }

    @Test(expected = ParseFailedExceptionSet.class)
    public void testNoKLabel() throws Exception {
        throwFirstLeftException(TermCons.apply(Arrays.asList(foo, bar), noKLabelProduction));
    }

    @Test
    public void testKList() throws Exception {
        assertCleanup(Ambiguity.apply(KList.apply(foo)), foo);
    }

    public void assertCleanup(Term input, Term expected) {
        Term actual = treeCleanerVisitor.apply(input);
        if (!actual.equals(expected)) {
            assertEquals(expected.toString(), actual.toString());
        }
    }

    public void throwFirstLeftException(Term input) {
        Term result = treeCleanerVisitor.apply(input);
        fail("Expected an exception but got:" + result);
    }

    @Test
    public void testMultipleExceptions() throws Exception {
        try {
            Term t = Ambiguity.apply(Ambiguity.apply(), KList.apply(Ambiguity.apply()));
            t = new CatchTransformer().apply(t);
            throw new AssertionError("Should have thrown an exception before this point.");
        } catch (ParseFailedExceptionSet e) {
            assertEquals("Should throw a set of 2 exceptions: ", 2, e.exceptions.size());
        }
    }
}