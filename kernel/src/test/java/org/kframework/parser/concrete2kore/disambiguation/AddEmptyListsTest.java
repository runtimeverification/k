// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Lists;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.Kompile;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;
import scala.util.Either;

import java.io.File;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class AddEmptyListsTest {
    private ParseInModule parser;

    @Rule
    public TestName testName = new TestName();

    @Before
    public void setUp() throws Exception {
        RuleGrammarGenerator gen = makeRuleGrammarGenerator();
        Module test = ParserUtils.parseMainModuleOuterSyntax(DEF, Source.apply("AddEmptyListsTest test definition"), "TEST");
        parser = gen.getCombinedGrammar(gen.getRuleGrammar(test));
    }

    /*
     * Return a RuleGrammarGenerator which uses the default K syntax as loaded from kast.k
     */
    private RuleGrammarGenerator makeRuleGrammarGenerator() {
        String definitionText;
        FileUtil files = FileUtil.testFileUtil();
        ParserUtils parser = new ParserUtils(files, new KExceptionManager(new GlobalOptions()));
        File definitionFile = new File(Kompile.BUILTIN_DIRECTORY.toString() + "/kast.k");
        definitionText = files.loadFromWorkingDirectory(definitionFile.getPath());

        Definition baseK =
                parser.loadDefinition("K", "K", definitionText,
                        definitionFile,
                        definitionFile.getParentFile(),
                        Lists.newArrayList(Kompile.BUILTIN_DIRECTORY),
                        true);

        return new RuleGrammarGenerator(baseK, true);
    }

    private void parseTerm(String term, String sort, K expected) {
        parseTerm(term, sort, expected, 0);
    }

    private void parseTerm(String term, String sort, K expected, int expectWarnings) {
        String source = "AddEmpytListsTest." + testName.getMethodName();
        final Tuple2<Either<Set<ParseFailedException>, K>, Set<ParseFailedException>> parseResult
                = parser.parseString(term, Sort(sort), new Source(source));
        if (parseResult._1().isLeft()) {
            Assert.assertTrue("Unexpected parse errors" + parseResult._1().left().get(), false);
        }
        K actual = TreeNodesToKORE.down(parseResult._1().right().get());
        Assert.assertEquals(expected, actual);
        if (parseResult._2().size() != expectWarnings) {
            Assert.assertTrue("Unexpected parse warnings" + parseResult._2(), false);
        }
    }

    private static final String DEF =
            "module TEST\n" +
                    "syntax A ::= \"a\" [klabel(\"alabel\")]\n" +
                    "syntax B ::= \"b\" [klabel(\"blabel\")]\n" +
                    "syntax A ::= B\n" +
                    "syntax As ::= List{A,\",\"}\n" +
                    "syntax Bs ::= List{B,\",\"}\n" +
                    "syntax As ::= Bs\n" +
                    "syntax K ::= f(As) | g(A) | h(Bs)" +
                    "endmodule\n";

    public static final KApply NIL = KApply(KLabel(".List{\"'_,_\"}"));
    public static final KLabel CONS = KLabel("_,_");
    public static final KApply A = KApply(KLabel("alabel"));
    public static final KApply B = KApply(KLabel("blabel"));
    public static final KLabel F = KLabel("f");
    public static final KLabel G = KLabel("g");
    public static final KLabel H = KLabel("h");
    public static final KLabel CAST_A = KLabel("#SemanticCastToA");
    public static final KLabel CAST_B = KLabel("#SemanticCastToB");
    public static final KLabel CAST_AS = KLabel("#SemanticCastToAs");
    public static final KLabel CAST_BS = KLabel("#SemanticCastToBs");

    @Test
    public void testEmptyList1() {
        parseTerm(".As", "As", NIL);
    }

    @Ignore("The API of AddEmptyLists needs to change for this to be possible")
    @Test
    public void testItem() {
        parseTerm("a", "As", KApply(CONS, A, NIL));
    }

    @Test
    public void testConcreteTop() {
        parseTerm(".As", "As", NIL);
        parseTerm("a,a", "As", KApply(CONS, A, KApply(CONS, A, NIL)));
        parseTerm("a,.As", "As", KApply(CONS, A, NIL));
        parseTerm("a,b", "As", KApply(CONS, A, KApply(CONS, B, NIL)));
        parseTerm("b,.Bs", "As", KApply(CONS, B, NIL));
        parseTerm("b,b", "As", KApply(CONS, B, KApply(CONS, B, NIL)));
    }

    @Test
    public void testConcreteArgument() {
        parseTerm("f(.As)", "K", KApply(F, NIL));
        parseTerm("f(a)", "K", KApply(F, KApply(CONS, A, NIL)));
        parseTerm("f(a,a)", "K", KApply(F, KApply(CONS, A, KApply(CONS, A, NIL))));
        parseTerm("f(a,.As)", "K", KApply(F, KApply(CONS, A, NIL)));
        parseTerm("f(a,b)", "K", KApply(F, KApply(CONS, A, KApply(CONS, B, NIL))));
        parseTerm("f(b,.Bs)", "K", KApply(F, KApply(CONS, B, NIL)));
        parseTerm("f(b,b)", "K", KApply(F, KApply(CONS, B, KApply(CONS, B, NIL))));
    }

    @Ignore("BUG: need to also propagate correct sorts to arguments of labeled application")
    @Test
    public void testLabeledFunSingleItem() {
        parseTerm("`f`(a)", "K", KApply(F, KApply(CONS, A, NIL)));
    }

    @Test
    public void testLabedFunConcreteArgument() {
        parseTerm("`f`(.As)", "K", KApply(F, NIL));
        parseTerm("`f`(`a,a`)", "K", KApply(F, KApply(CONS, A, KApply(CONS, A, NIL))));
        parseTerm("`f`(`a,.As`)", "K", KApply(F, KApply(CONS, A, NIL)));
        parseTerm("`f`(`a,b`)", "K", KApply(F, KApply(CONS, A, KApply(CONS, B, NIL))));
        parseTerm("`f`(`b,.Bs`)", "K", KApply(F, KApply(CONS, B, NIL)));
        parseTerm("`f`(`b,b`)", "K", KApply(F, KApply(CONS, B, KApply(CONS, B, NIL))));
    }

    @Test
    public void testAnnVar() {
        parseTerm("V:As", "K", KApply(CAST_AS, KVariable("V")));
    }

    @Test
    public void testArgumentLabeledCons() {
        parseTerm("f(`_,_`(a,.As))", "K", KApply(F, KApply(CONS, A, NIL)));
    }

    @Test
    public void testArgumentLabeledNil() {
        parseTerm("f(`.List{\"'_,_\"}`(.KList))", "K", KApply(F, NIL));
    }

    @Test
    public void testArgumentLabeledConsSub1() {
        parseTerm("h(`_,_`(b,.Bs))", "K", KApply(H, KApply(CONS, B, NIL)));
    }

    @Test
    public void testArgumentLabeledConsSub2() {
        // gets a warning because the argument of sort As does not fit.n
        parseTerm("h(`_,_`(a,.As))", "K", KApply(H, KApply(CONS, A, NIL)), 1);
    }

    @Test
    public void testArgumentLabeledNilSub1() {
        parseTerm("h(`.List{\"'_,_\"}`(.KList))", "K", KApply(H, NIL));
    }

    @Test
    public void testArgumentInferredListVar() {
        // 1 warning from inference
        parseTerm("f(V)", "K", KApply(F, KApply(CAST_AS, KVariable("V"))), 1);
    }

    @Test
    public void testArgumentAnnListVar() {
        parseTerm("f(V:As)", "K", KApply(F, KApply(CAST_AS, KVariable("V"))));
    }

    @Test
    public void testArgumentAnnSubListVar() {
        parseTerm("f(V:Bs)", "K", KApply(F, KApply(CAST_BS, KVariable("V"))));
    }

    @Test
    public void testArgumentInferredItemVar() {
        // 1 warning from inference
        parseTerm("f(V)~>g(V)", "K",
                KSequence(KApply(F, KApply(CONS, KApply(CAST_A, KVariable("V")), NIL)),
                        KApply(G, KApply(CAST_A, KVariable("V")))), 1);
    }

    @Test
    public void testArgumentAnnItemVar() {
        parseTerm("f(V:A)", "K",
                KApply(F, KApply(CONS, KApply(CAST_A, KVariable("V")), NIL)));
    }

    @Test
    public void testArgumentAnnSubItemVar() {
        parseTerm("f(V:B)", "K",
                KApply(F, KApply(CONS, KApply(CAST_B, KVariable("V")), NIL)));
    }
}
