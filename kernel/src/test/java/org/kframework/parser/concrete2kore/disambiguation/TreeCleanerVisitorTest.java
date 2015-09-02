// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.concrete2kore.disambiguation;

import org.junit.Test;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.KList;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.pcollections.ConsPStack;
import scala.util.Either;

import java.util.Arrays;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;
import static org.kframework.Collections.Seq;
import static org.kframework.definition.Constructors.NonTerminal;
import static org.kframework.definition.Constructors.Production;
import static org.kframework.definition.Constructors.RegexTerminal;
import static org.kframework.kore.KORE.Sort;

public class TreeCleanerVisitorTest {


    TreeCleanerVisitor treeCleanerVisitor = new TreeCleanerVisitor();
    org.kframework.definition.Production fooProduction = Production(Sort("Foo"), Seq(RegexTerminal("foo|bar")));
    Constant foo = Constant.apply("foo", fooProduction);
    Constant bar = Constant.apply("bar", fooProduction);

    org.kframework.definition.Production noKLabelProduction = Production(Sort("NoKLabelProd"), Seq(NonTerminal(Sort("Foo")), NonTerminal(Sort("Foo"))));

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

    @Test(expected = ParseFailedException.class)
    public void testNoKLabel() throws Exception {
        throwFirstLeftException(TermCons.apply(ConsPStack.from(Arrays.asList(bar, foo)), noKLabelProduction, new Location(0, 0, 0, 0), new Source("")));
    }

    @Test
    public void testKList() throws Exception {
        assertCleanup(Ambiguity.apply(KList.apply(ConsPStack.singleton(foo))), foo);
    }

    public void assertCleanup(Term input, Term expected) {
        Term actual = treeCleanerVisitor.apply(input).right().get();
        if (!actual.equals(expected)) {
            assertEquals(expected.toString(), actual.toString());
        }
    }

    public void throwFirstLeftException(Term input) {
        Either<Set<ParseFailedException>, Term> result = treeCleanerVisitor.apply(input);
        if (result.isRight()) {
            fail("Expected an exception but got:" + result.right().get());
        } else {
            throw result.left().get().iterator().next();
        }
    }
}
