// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.Collections;
import org.kframework.compiler.StrictToHeatingCooling;
import org.kframework.definition.Bubble;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.kil.Sources;
import org.kframework.kore.KApply;
import org.kframework.kore.Unparse;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.RuleGrammarTest;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.tiny.And;
import org.kframework.tiny.Constructors;
import org.kframework.tiny.FreeTheory;
import org.kframework.tiny.K;
import org.kframework.tiny.KApp;
import org.kframework.tiny.KIndex$;
import org.kframework.tiny.Or;
import org.kframework.tiny.Rewriter;
import org.kframework.tiny.Rule;
import org.kframework.tiny.package$;
import scala.collection.immutable.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;


public class TstTinyOnKORE {

    public static final File BUILTIN_DIRECTORY = new File("k-distribution/include/builtin").getAbsoluteFile();
    @org.junit.Rule
    public TestName name = new TestName();
    private static final String mainModule = "K";
    private static final String startSymbol = "RuleContent";


    protected File testResource(String baseName) {
        return new File(new File("k-distribution/src/test/resources" + baseName)
                .getAbsoluteFile().toString().replace("k-distribution" + File.separator + "k-distribution", "k-distribution"));
        // a bit of a hack to get around not having a clear working directory
        // Eclipse runs tests within k/k-distribution, IntelliJ within /k
    }

    public RuleGrammarGenerator makeRuleGrammarGenerator() throws URISyntaxException {
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(new File(BUILTIN_DIRECTORY.toString() + "/kast.k"));
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        Module baseK = ParserUtils.parseMainModuleOuterSyntax(definitionText, mainModule);
        return new RuleGrammarGenerator(baseK);
    }

    @Test
    public void kore_imp_tiny() throws IOException, URISyntaxException {
//        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
//        Module moduleWithoutK = kilToKore.apply(defWithContext.definition).getModule("TEST").get();
//
//        Module module = Module("IMP", Set(moduleWithoutK), Set(
//                Production(Sort("K"), Seq(NonTerminal(Sort("KSequence"))))
//        ), Att());

        File definitionFile = testResource("/convertor-tests/" + name.getMethodName() + ".k");
        String definitionString = FileUtils.readFileToString(definitionFile);

        RuleGrammarGenerator gen = makeRuleGrammarGenerator();

//        Module mainModuleWithBubble = ParserUtils.parseMainModuleOuterSyntax(definitionString, "TEST");

        Definition kastDefintion = Definition(immutable(ParserUtils.loadModules(definitionString,
                Sources.fromFile(BUILTIN_DIRECTORY.toPath().resolve("kast.k").toFile()),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY))));

        java.util.Set<Module> modules =
                ParserUtils.loadModules(definitionString, Sources.fromFile(definitionFile),
                        definitionFile.getParentFile(),
                        Lists.newArrayList(BUILTIN_DIRECTORY));

        Module mainModuleWithBubble = modules.stream().filter(m -> m.name().equals("TEST")).findFirst().get();

        ParseInModule ruleParser = gen.getRuleGrammar(mainModuleWithBubble);

        scala.collection.immutable.Set<org.kframework.definition.Sentence> ruleSet = stream(mainModuleWithBubble.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> ((Bubble) b).contents())
                .map(s -> ruleParser.parseString(s, startSymbol))
                .map(result -> {
                    System.out.println("warning = " + result._2());
                    if (result._1().isRight())
                        return result._1().right().get();
                    else {
                        throw new AssertionError("Found error: " + result._1().left().get());
                    }
                })
                .map(TreeNodesToKORE::apply)
                .map(TreeNodesToKORE::down)
                .map(contents -> {
                    KApply ruleContents = (KApply) contents;
                    List<org.kframework.kore.K> items = ruleContents.klist().items();
                    switch (ruleContents.klabel().name()) {
                        case "#ruleNoConditions":
                            return Rule(items.get(0), And.apply(), Or.apply());
                        case "#ruleRequires":
                            return Rule(items.get(0), items.get(1), Or.apply());
                        case "#ruleEnsures":
                            return Rule(items.get(0), And.apply(), items.get(1));
                        case "#ruleRequiresEnsures":
                            return Rule(items.get(0), items.get(1), items.get(2));
                        default:
                            throw new AssertionError("Wrong KLabel for rule content");
                    }
                })
                .collect(Collections.toSet());


        Module mainModule = Module("TEST", Set(),
                (scala.collection.immutable.Set<org.kframework.definition.Sentence>) mainModuleWithBubble.sentences().$bar(ruleSet), Att());

//        return parser.parseString(input, startSymbol);

        Constructors cons = new Constructors(mainModule);

        K program = cons.KLabel("<top>").apply(
                cons.KLabel("<k>").apply(
                        cons.KLabel("while__").apply(
                                cons.KLabel("_<=_").apply((K) cons.intToToken(0), (K) cons.stringToId("n")),
                                cons.KLabel("__").apply(
                                        cons.KLabel("_=_;").apply(
                                                (K) cons.stringToId("s"),
                                                cons.KLabel("_+_").apply(
                                                        (K) cons.stringToId("s"),
                                                        (K) cons.stringToId("n"))),
                                        cons.KLabel("_=_;").apply(
                                                (K) cons.stringToId("n"),
                                                cons.KLabel("_+_").apply(
                                                        (K) cons.stringToId("n"),
                                                        (K) cons.intToToken(-1)))
                                ))),
                cons.KLabel("<state>").apply(
                        cons.KLabel("_Map_").apply(
                                cons.KLabel("_|->_").apply((K) cons.stringToId("n"), (K) cons.intToToken(10)),
                                cons.KLabel("_|->_").apply((K) cons.stringToId("s"), (K) cons.intToToken(0)))
                )
        );

//        KApp program = cons.KApply(cons.KLabel("'<top>"),
//                cons.KApply(cons.KLabel("'<k>"),
//                        cons.KApply(cons.KLabel("'_/_"), cons.stringToId("x"), cons.stringToId("y"))),
//                        cons.KApply(cons.KLabel("'<state>"),
//                                cons.KApply(cons.KLabel("'_Map_"),
//                                        cons.KApply(cons.KLabel("'_|->_"), cons.stringToId("x"), cons.intToToken(10)),
//                                        cons.KApply(cons.KLabel("'_|->_"), cons.stringToId("y"), cons.intToToken(2)))
//                        ));


//        System.out.println("module = " + mainModule);

        Module afterHeatingCooling = StrictToHeatingCooling.apply(mainModule);

        Module withKSeq = Module("EXECUTION",
                Set(afterHeatingCooling, kastDefintion.getModule("KSEQ").get()),
                Collections.<Sentence>Set(), Att());

        System.out.println(">>>>>\n" + afterHeatingCooling.rules().mkString("\n"));

        Rewriter rewriter = new Rewriter(withKSeq, KIndex$.MODULE$);

//        long l = System.nanoTime();
//        Set<K> results = rewriter.rewrite(program, Set());
//        System.out.println("time = " + (System.nanoTime() - l) / 1000000);
//
//        return stream(results).map(r -> r.toString()).collect(Collections.toList()).mkString("\n");

        long l = System.nanoTime();
        K result = rewriter.execute(program);
        System.out.println("time = " + (System.nanoTime() - l) / 1000000);

        System.out.println("result = " + result.toString());
    }
}
