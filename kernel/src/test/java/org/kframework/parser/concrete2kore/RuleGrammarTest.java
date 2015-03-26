// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kil.Sources;
import org.kframework.main.GlobalOptions;
import org.kframework.main.GlobalOptions.Warnings;
import org.kframework.parser.Term;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import scala.Tuple2;
import scala.util.Either;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

public class RuleGrammarTest {
    private File definitionFile = null;
    private Definition baseK = null;
    private final static String startSymbol = "RuleContent";
    private RuleGrammarGenerator gen;
    private final boolean printout = false;
    public static final File BUILTIN_DIRECTORY = new File("k-distribution/include/builtin").getAbsoluteFile();

    @Before
    public void setUp() throws  Exception{
        definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/kast.k");

        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        java.util.Set<Module> modules =
                ParserUtils.loadModules(definitionText,
                        Sources.fromFile(definitionFile),
                        definitionFile.getParentFile(),
                        Lists.newArrayList(BUILTIN_DIRECTORY));

        baseK = Definition(immutable(modules));
        gen = new RuleGrammarGenerator(baseK);
    }

    private void printout(Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule, int warnings, boolean error) {
        if (printout) {
            KExceptionManager kem = new KExceptionManager(new GlobalOptions(true, Warnings.ALL, true));
            if (rule._1().isLeft()) {
                for (ParseFailedException x : rule._1().left().get()) {
                    kem.addKException(x.getKException());
                }
            } else {
                System.err.println("rule = " + rule._1().right().get());
            }
            for (ParseFailedException x : rule._2()) {
                kem.addKException(x.getKException());
            }
            kem.print();
        }
        Assert.assertEquals("Expected " + warnings + " warnings: ", warnings, rule._2().size());
        if (error)
            Assert.assertTrue("Expected error here: ", rule._1().isLeft());
        else
            Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
    }

    private Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> parseRule(String def, String input) {
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        return parser.parseString(input, startSymbol);
    }

    @Test
    public void test1() {
        Assert.assertNotNull(definitionFile);
    }

    // test proper associativity for rewrite, ~> and cast
    @Test
    public void test2() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), left] " +
                "| r\"[0-9]+\" [token] " +
                "syntax left 'Plus " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "1+2=>A:Exp~>B:>Exp");
        printout(rule, 1, false);
    }

    // test variable disambiguation when a variable is declared by the user
    @Test
    public void test3() {
        String def = "" +
                "module TEST " +
                "syntax Exps ::= Exp \",\" Exps [klabel('Exps)] " +
                "| Exp " +
                "syntax Exp ::= Id " +
                "syntax Stmt ::= \"val\" Exps \";\" Stmt [klabel('Decl)] " +
                "syntax KBott ::= \"(\" K \")\" [bracket, klabel('bracket)] " +
                "| (Id, Stmt) [klabel('tuple)] " +
                "syntax Id " +
                "syntax K " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "val X ; S:Stmt => (X, S)");
        printout(rule, 1, false);
    }

    // test variable disambiguation when all variables are being inferred
    @Test
    public void test4() {
        String def = "" +
                "module TEST " +
                "syntax Exps ::= Exp \",\" Exps [klabel('Exps)] " +
                "| Exp " +
                "syntax Exp ::= Id " +
                "syntax Stmt ::= \"val\" Exps \";\" Stmt [klabel('Decl)] " +
                "syntax KBott ::= \"(\" K \")\" [bracket, klabel('bracket)] " +
                "| (Id, Stmt) [klabel('tuple)] " +
                "syntax Id " +
                "syntax K " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "val X ; S => (X, S)");
        printout(rule, 2, false);
    }

    // test error reporting when + is non-associative
    @Test
    public void test5() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), non-assoc] " +
                "| r\"[0-9]+\" [token] " +
                "syntax non-assoc 'Plus " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "1+2+3");
        printout(rule, 0, true);
    }

    // test AmbFilter which should report ambiguities and return a clean term
    @Test
    public void test6() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus)] " +
                "| r\"[0-9]+\" [token] " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "1+2+3");
        Assert.assertEquals("Expected 1 warning: ", 1, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        printout(rule, 1, false);
    }

    // test error reporting when rewrite priority is not met
    @Test
    public void test7() {
        String def = "" +
                "module TEST " +
                "syntax A ::= \"foo\" A [klabel('foo)] " +
                "syntax B ::= \"bar\"   [klabel('bar)] " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "foo bar => X");
        printout(rule, 0, true);
    }

    // test prefer and avoid
    @Test
    public void test8() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), prefer] " +
                "| Exp \"*\" Exp [klabel('Mul)] " +
                "| r\"[0-9]+\" [token] " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "1+2*3");
        Assert.assertEquals("Expected 0 warnings: ", 0, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        printout(rule, 0, false);
    }

    // test cells
    @Test
    public void test9() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), prefer] " +
                "| Exp \"*\" Exp [klabel('Mul)] " +
                "| r\"[0-9]+\" [token] " +
                "syntax K " +
                "syntax TopCell ::= \"<T>\" KCell StateCell \"</T>\" [klabel(<T>), cell] " +
                "syntax KCell ::= \"<k>\" K \"</k>\" [klabel(<k>), cell] " +
                "syntax StateCell ::= \"<state>\" K \"</state>\" [klabel(<state>), cell] " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "<T> <k>...1+2*3...</k> `<state> A => .::K ...</state> => .::Bag` ...</T>");
        printout(rule, 1, false);
    }

    // test cells
    @Test
    public void test10() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \",\" Exp [klabel('Plus), prefer] " +
                "| Exp \"*\" Exp [klabel('Mul)] " +
                "| r\"[0-9]+\" [token] " +
                "endmodule";
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule = parseRule(def, "A::KLabel(B::K, C::K, D::K)");
        printout(rule, 1, false);
    }
}
