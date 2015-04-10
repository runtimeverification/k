// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.kframework.Collections;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.compile.ModuleTransformation;
import org.kframework.compile.StrictToHeatingCooling;
import org.kframework.definition.Bubble;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.kil.Sources;
import org.kframework.kore.compile.*;
import org.kframework.compile.LabelInfo;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.tiny.*;
import org.kframework.utils.file.JarInfo;
import scala.Tuple2;
import scala.collection.immutable.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.List;
import java.util.function.Function;

public class Kompile {

    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
    private static final String mainModule = "K";
    private static final String startSymbol = "RuleContent";

    private static RuleGrammarGenerator makeRuleGrammarGenerator() throws URISyntaxException, IOException {
        String definitionText;
        File definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/kast.k");
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        //Definition baseK = ParserUtils.parseMainModuleOuterSyntax(definitionText, mainModule);
        java.util.Set<Module> modules =
                ParserUtils.loadModules(definitionText,
                        Sources.fromFile(definitionFile),
                        definitionFile.getParentFile(),
                        Lists.newArrayList(BUILTIN_DIRECTORY));

        return new RuleGrammarGenerator(modules);
    }

    public static org.kframework.tiny.Rewriter getRewriter(Module module) throws IOException, URISyntaxException {

        return new org.kframework.tiny.Rewriter(module, KIndex$.MODULE$);
    }

    // todo: rename and refactor this
    public static Tuple2<Module, Function<String, K>> getStuff(File definitionFile, String mainModuleName, String mainProgramsModule) throws IOException, URISyntaxException {
        String definitionString = FileUtils.readFileToString(definitionFile);

//        Module mainModuleWithBubble = ParserUtils.parseMainModuleOuterSyntax(definitionString, "TEST");

        Definition definition = ParserUtils.loadDefinition(
                mainModuleName,
                mainProgramsModule, definitionString,
                Sources.fromFile(definitionFile),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY));

        Module mainModuleWithBubble = stream(definition.modules()).filter(m -> m.name().equals(mainModuleName)).findFirst().get();

        RuleGrammarGenerator gen = makeRuleGrammarGenerator();
        ParseInModule ruleParser = gen.getRuleGrammar(mainModuleWithBubble);

        Set<Sentence> ruleSet = stream(mainModuleWithBubble.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .map(b -> {
                    int startLine = b.att().<Integer>get("contentStartLine").get();
                    int startColumn = b.att().<Integer>get("contentStartColumn").get();
                    return ruleParser.parseString(b.contents(), startSymbol, startLine, startColumn);
                })
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

        // todo: Cosmin: fix as this effectively flattens the module
        Module mainModule = Module(mainModuleName, Set(),
                (Set<Sentence>) mainModuleWithBubble.sentences().$bar(ruleSet), Att());

        Module afterHeatingCooling = StrictToHeatingCooling.apply(mainModule);

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(afterHeatingCooling);
        LabelInfo labelInfo = new LabelInfoFromModule(afterHeatingCooling);
        SortInfo sortInfo = SortInfo.fromModule(afterHeatingCooling);

        Module withTopCells = new AddImplicitCells(configInfo, labelInfo).addImplicitCells(afterHeatingCooling);
        Module concretized = new ConcretizeConfiguration(configInfo, labelInfo).concretize(withTopCells);
        Module closed = new CloseCells(configInfo, sortInfo, labelInfo).close(concretized);
        Module sorted = new SortCells(configInfo, labelInfo).sortCells(closed);

        Module kseqModule = ParserUtils.loadModules("requires \"kast.k\"",
                Sources.fromFile(BUILTIN_DIRECTORY.toPath().resolve("kast.k").toFile()),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY)).stream().filter(m -> m.name().equals("KSEQ")).findFirst().get();

        Module withKSeq = Module("EXECUTION",
                Set(sorted, kseqModule),
                Collections.<Sentence>Set(), Att());

        Module moduleForPrograms = definition.getModule(mainProgramsModule).get();
        ParseInModule parseInModule = RuleGrammarGenerator.getProgramsGrammar(moduleForPrograms);

        final Function<String, K> pp = s -> {
            return TreeNodesToKORE.down(TreeNodesToKORE.apply(parseInModule.parseString(s, "K")._1().right().get()));
        };

        return Tuple2.apply(withKSeq, pp);
    }
}
