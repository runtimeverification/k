// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.parser.concrete2kore;

import org.junit.Test;
import org.kframework.kore.outer.SyntaxProduction;
import org.kframework.parser.*;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.util.Either;

import java.util.Arrays;
import java.util.Optional;
import java.util.Set;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.Collections.*;

import static org.junit.Assert.*;

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

    @Test(expected = ParseFailedException.class)
    public void testNoKLabel() throws Exception {
        throwFirstLeftException(TermCons.apply(Arrays.asList(foo, bar), noKLabelProduction));
    }

    @Test
    public void testKList() throws Exception {
        assertCleanup(Ambiguity.apply(KList.apply(foo)), foo);
    }


//        amb([amb([NOKLABEL(amb([#emptyKRequireList()]),amb([#KModuleList(amb([#KModule(amb([#token(KModuleName,"FOO ")]),amb([#emptyKImportList()]),amb([#emptyKSentenceList()]))]),amb([#emptyKModuleList()]))]))])])

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

    @Test
    public void testMerge() throws Exception {

    }
}