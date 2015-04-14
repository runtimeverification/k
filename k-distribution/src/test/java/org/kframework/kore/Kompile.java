// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore;

import com.beust.jcommander.internal.Lists;
import org.apache.commons.io.FileUtils;
import org.kframework.Collections;
import org.kframework.attributes.Source;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.compile.StrictToHeatingCooling;
import org.kframework.definition.Bubble;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Sentence;
import org.kframework.kore.compile.*;
import org.kframework.compile.LabelInfo;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.tiny.*;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import scala.Tuple2;
import scala.collection.immutable.Set;
import scala.util.Either;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.UnaryOperator;

/**
 * The new compilation pipeline. Everything is just wired together and will need clean-up once we deside on design.
 * Tracked by #1442.
 */

public class Kompile {

    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
    private static final String mainModule = "K";
    private static final String startSymbol = "RuleContent";

    private final FileUtil files;
    private final ParserUtils parser;

    public Kompile(FileUtil files) {
        this.files = files;
        this.parser = new ParserUtils(files);
        gen = makeRuleGrammarGenerator();
    }

    private RuleGrammarGenerator makeRuleGrammarGenerator() {
        File definitionFile = new File(BUILTIN_DIRECTORY.toString() + "/kast.k");
        String definitionText = files.loadFromWorkingDirectory(definitionFile.getPath());

        //Definition baseK = ParserUtils.parseMainModuleOuterSyntax(definitionText, mainModule);
        java.util.Set<Module> modules =
                parser.loadModules(definitionText,
                        Source.apply(definitionFile.getPath()),
                        definitionFile.getParentFile(),
                        Lists.newArrayList(BUILTIN_DIRECTORY));

        return new RuleGrammarGenerator(modules);
    }

    public static org.kframework.tiny.Rewriter getRewriter(Module module) throws IOException, URISyntaxException {
        return new org.kframework.tiny.Rewriter(module, KIndex$.MODULE$);
    }

    // todo: rename and refactor this
    public Tuple2<Module, BiFunction<String, Source, K>> getStuff(File definitionFile, String mainModuleName, String mainProgramsModule) throws IOException, URISyntaxException {
        String definitionString = FileUtils.readFileToString(definitionFile);

//        Module mainModuleWithBubble = ParserUtils.parseMainModuleOuterSyntax(definitionString, "TEST");

        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, definitionString,
                Source.apply(definitionFile.getPath()),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY));

        Module mainModuleWithBubble = stream(definition.modules()).filter(m -> m.name().equals(mainModuleName)).findFirst().get();

        Module mainModule = ModuleTransformer.from(this::resolveBubbles).apply(mainModuleWithBubble);

        Module afterHeatingCooling = StrictToHeatingCooling.apply(mainModule);

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(afterHeatingCooling);
        LabelInfo labelInfo = new LabelInfoFromModule(afterHeatingCooling);
        SortInfo sortInfo = SortInfo.fromModule(afterHeatingCooling);

        Module concretized = new ConcretizeCells(configInfo, labelInfo, sortInfo).concretize(afterHeatingCooling);

        Module kseqModule = parser.loadModules("requires \"kast.k\"",
                Source.apply(BUILTIN_DIRECTORY.toPath().resolve("kast.k").toFile().getPath()),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY)).stream().filter(m -> m.name().equals("KSEQ")).findFirst().get();

        Module withKSeq = Module("EXECUTION",
                Set(concretized, kseqModule),
                Collections.<Sentence>Set(), Att());

        Module moduleForPrograms = definition.getModule(mainProgramsModule).get();
        ParseInModule parseInModule = gen.getProgramsGrammar(moduleForPrograms);

        final BiFunction<String, Source, K> pp = (s, source) -> {
            Tuple2<Either<java.util.Set<ParseFailedException>, Term>, java.util.Set<ParseFailedException>> result = parseInModule.parseString(s, "K", source);
            return TreeNodesToKORE.down(TreeNodesToKORE.apply(result._1().right().get()));
        };

        System.out.println(concretized);

        return Tuple2.apply(withKSeq, pp);
    }

    RuleGrammarGenerator gen;

    private Module resolveBubbles(Module mainModuleWithBubble) {

        ParseInModule ruleParser = gen.getRuleGrammar(mainModuleWithBubble);

        Set<Sentence> ruleSet = stream(mainModuleWithBubble.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .map(b -> {
                    int startLine = b.att().<Integer>get("contentStartLine").get();
                    int startColumn = b.att().<Integer>get("contentStartColumn").get();
                    String source = b.att().<String>get("Source").get();
                    return ruleParser.parseString(b.contents(), startSymbol, Source.apply(source), startLine, startColumn);
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
        return Module(mainModuleWithBubble.name(), mainModuleWithBubble.imports(),
                (Set<Sentence>) mainModuleWithBubble.localSentences().$bar(ruleSet), mainModuleWithBubble.att());
    }
}
