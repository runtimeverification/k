// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.definition.Module;
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

public class RuleGrammarTest {
    private File definitionFile = null;
    private Module baseK = null;
    private final static String mainModule = "K";
    private final static String startSymbol = "KList";
    private RuleGrammarGenerator gen;
    private final boolean printout = false;

    @Before
    public void setUp() throws  Exception{
        definitionFile = new File(RuleGrammarTest.class.getResource
                ("/kast.k").toURI()).getAbsoluteFile();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        baseK = ParserUtils.parseMainModuleOuterSyntax(definitionText, mainModule);
        gen = new RuleGrammarGenerator(baseK);
    }

    private void printout(Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule) {
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
        Assert.assertEquals("Expected 0 warnings: ", 1, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        printout(rule);
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
        Assert.assertEquals("Expected 1 warning: ", 1, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        printout(rule);
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
        Assert.assertEquals("Expected 2 warnings: ", 2, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        printout(rule);
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
        Assert.assertEquals("Expected 0 warnings: ", 0, rule._2().size());
        Assert.assertTrue("Expected error here: ", rule._1().isLeft());
        printout(rule);
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
        printout(rule);
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
        Assert.assertEquals("Expected 0 warning: ", 0, rule._2().size());
        Assert.assertTrue("Expected errors here: ", rule._1().isLeft());
        printout(rule);
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
        printout(rule);
    }
}
