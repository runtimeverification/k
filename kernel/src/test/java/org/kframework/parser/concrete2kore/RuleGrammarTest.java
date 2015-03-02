// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.definition.Module;
import org.kframework.parser.Term;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
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

    @Test
    public void test1() {
        Assert.assertNotNull(definitionFile);
    }

    @Test
    public void test2() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), left] " +
                "| r\"[0-9]+\" [token] " +
                "syntax left 'Plus " +
                "endmodule";
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        Term rule = parser.parseString("1+2=>A:Exp~>B:>Exp", startSymbol)._1().right().get();
        System.out.println("rule = " + rule);
    }

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
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule =
                parser.parseString("val X ; S:Stmt => (X, S)", startSymbol);
        Assert.assertEquals("Expected 1 warning: ", 1, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        System.out.println("rule = " + rule._1().right().get());
    }

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
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule =
                parser.parseString("val X ; S => (X, S)", startSymbol);
        Assert.assertEquals("Expected 2 warnings: ", 2, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
        System.out.println("rule = " + rule._1().right().get());
    }

    @Test
    public void test5() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus), non-assoc] " +
                "| r\"[0-9]+\" [token] " +
                "syntax non-assoc 'Plus " +
                "endmodule";
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule =
                parser.parseString("1+2+3", startSymbol);
        Assert.assertEquals("Expected 0 warnings: ", 0, rule._2().size());
        Assert.assertTrue("Expected error here: ", rule._1().isLeft());
    }

    @Test
    public void test6() {
        String def = "" +
                "module TEST " +
                "syntax Exp ::= Exp \"+\" Exp [klabel('Plus)] " +
                "| r\"[0-9]+\" [token] " +
                "endmodule";
        Module test = ParserUtils.parseMainModuleOuterSyntax(def, "TEST");
        ParseInModule parser = gen.getRuleGrammar(test);
        Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rule =
                parser.parseString("1+2+3", startSymbol);
        Assert.assertEquals("Expected 1 warning: ", 1, rule._2().size());
        Assert.assertTrue("Expected no errors here: ", rule._1().isRight());
    }
}
