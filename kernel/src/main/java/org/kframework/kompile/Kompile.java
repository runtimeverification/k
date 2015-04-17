// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfo;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.compile.StrictToHeatingCooling;
import org.kframework.definition.Bubble;
import org.kframework.definition.Configuration;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.compile.ConcretizeCells;
import org.kframework.kore.compile.GenerateSentencesFromConfigDecl;
import org.kframework.kore.compile.SortInfo;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import scala.Tuple2;
import scala.Tuple3;
import scala.collection.Seq;
import scala.collection.immutable.Set;
import scala.util.Either;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.definition.Constructors.*;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The new compilation pipeline. Everything is just wired together and will need clean-up once we deside on design.
 * Tracked by #1442.
 */

public class Kompile {

    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
    private static final String REQUIRE_KAST_K = "requires \"kast.k\"\n";
    private static final String mainModule = "K";
    private static final String startSymbol = "RuleContent";

    private final FileUtil files;
    private final KExceptionManager kem;
    private final ParserUtils parser;

    @Inject
    public Kompile(FileUtil files, KExceptionManager kem) {
        this.files = files;
        this.kem = kem;
        this.parser = new ParserUtils(files);
    }

    /**
     * Executes the Kompile tool. This tool accesses a
     * @param definitionFile
     * @param mainModuleName
     * @param mainProgramsModule
     * @param programStartSymbol
     * @return
     */
    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModule, String programStartSymbol) {
        Definition defWithConfig = parseDefinition(definitionFile, mainModuleName, mainProgramsModule, true);

        Module mainModule = ModuleTransformer.from(this::resolveBubbles).apply(defWithConfig.mainModule());
        Module afterHeatingCooling = StrictToHeatingCooling.apply(mainModule);

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(afterHeatingCooling);
        LabelInfo labelInfo = new LabelInfoFromModule(afterHeatingCooling);
        SortInfo sortInfo = SortInfo.fromModule(afterHeatingCooling);

        Module concretized = new ConcretizeCells(configInfo, labelInfo, sortInfo).concretize(afterHeatingCooling);

        Module kseqModule = defWithConfig.getModule("KSEQ").get();

        Module withKSeq = Module("EXECUTION",
                Set(concretized, kseqModule),
                Collections.<Sentence>Set(), Att());

        final BiFunction<String, Source, K> pp = getProgramParser(defWithConfig.getModule(mainProgramsModule).get(), programStartSymbol);

        System.out.println(concretized);

        return new CompiledDefinition(withKSeq, defWithConfig, pp);
    }

    public BiFunction<String, Source, K> getProgramParser(Module moduleForPrograms, String programStartSymbol) {
        ParseInModule parseInModule = gen.getProgramsGrammar(moduleForPrograms);

        return (s, source) -> {
            return TreeNodesToKORE.down(TreeNodesToKORE.apply(parseInModule.parseString(s, programStartSymbol, source)._1().right().get()));
        };
    }

    public Definition parseDefinition(File definitionFile, String mainModuleName, String mainProgramsModule, boolean dropQuote) {
        String definitionString = files.loadFromWorkingDirectory(definitionFile.getPath());

        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, REQUIRE_KAST_K + definitionString,
                Source.apply(definitionFile.getPath()),
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY),
                dropQuote);

        boolean hasConfigDecl = stream(definition.mainModule().sentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config"))
                .findFirst().isPresent();

        Definition definitionWithConfigBubble;
        if (!hasConfigDecl) {
            definitionWithConfigBubble = DefinitionTransformer.from(mod -> {
                if (mod == definition.mainModule()) {
                    return Module(mod.name(), (Set<Module>) mod.imports().$plus(definition.getModule("DEFAULT-CONFIGURATION").get()), mod.localSentences(), mod.att());
                }
                return mod;
            }).apply(definition);
        } else {
            definitionWithConfigBubble = definition;
        }

        errors = Sets.newHashSet();
        gen = new RuleGrammarGenerator(definitionWithConfigBubble);
        Definition defWithConfig = DefinitionTransformer.from(this::resolveConfig).apply(definitionWithConfigBubble);

        gen = new RuleGrammarGenerator(defWithConfig);

        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.getKException()).collect(Collectors.toList()));
            throw KExceptionManager.compilerError("Had " + errors.size() + " parsing errors.");
        }
        return defWithConfig;
    }

    java.util.Set<ParseFailedException> errors;
    RuleGrammarGenerator gen;

    K _true = KToken(Sort("KBool"), "KTrue");

    private Module resolveConfig(Module module) {
        ParseInModule configParser = gen.getConfigGrammar(module);

        Set<Sentence> configDeclProductions = stream(module.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config"))
                .map(b -> {
                    int startLine = b.att().<Integer>get("contentStartLine").get();
                    int startColumn = b.att().<Integer>get("contentStartColumn").get();
                    String source = b.att().<String>get("Source").get();
                    return configParser.parseString(b.contents(), startSymbol, Source.apply(source), startLine, startColumn);
                })
                .flatMap(result -> {
                    kem.addAllKException(result._2().stream().map(e -> e.getKException()).collect(Collectors.toList()));
                    if (result._1().isRight())
                        return Stream.of(result._1().right().get());
                    else {
                        errors.addAll(result._1().left().get());
                        return Stream.empty();
                    }
                })
                .map(TreeNodesToKORE::apply)
                .map(TreeNodesToKORE::down)
                .map(contents -> {
                    KApply configContents = (KApply) contents;
                    List<org.kframework.kore.K> items = configContents.klist().items();
                    switch (configContents.klabel().name()) {
                    case "#ruleNoConditions":
                        return Configuration(items.get(0), _true, Att.apply());
                    case "#ruleEnsures":
                        return Configuration(items.get(0), items.get(1), Att.apply());
                    default:
                        throw new AssertionError("Wrong KLabel for rule content");
                    }
                })
                .flatMap(
                        configDecl -> stream(GenerateSentencesFromConfigDecl.gen(configDecl.body(), configDecl.ensures(), configDecl.att(), configParser.module())))
                .collect(Collections.toSet());
        return Module(module.name(), module.imports(), (Set<Sentence>) module.localSentences().$bar(configDeclProductions), module.att());
    }

    private Module resolveBubbles(Module mainModuleWithBubble) {
        ParseInModule ruleParser = gen.getRuleGrammar(mainModuleWithBubble);

        Set<Sentence> ruleSet = stream(mainModuleWithBubble.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> !b.sentenceType().equals("config"))
                .map(b -> {
                    int startLine = b.att().<Integer>get("contentStartLine").get();
                    int startColumn = b.att().<Integer>get("contentStartColumn").get();
                    String source = b.att().<String>get("Source").get();
                    return ruleParser.parseString(b.contents(), startSymbol, Source.apply(source), startLine, startColumn);
                })
                .flatMap(result -> {
                    if (result._1().isRight()) {
                        kem.addAllKException(result._2().stream().map(e -> e.getKException()).collect(Collectors.toList()));
                        return Stream.of(result._1().right().get());
                    } else {
                        errors.addAll(result._1().left().get());
                        return Stream.empty();
                    }
                })
                .map(TreeNodesToKORE::apply)
                .map(TreeNodesToKORE::down)
                .map(contents -> {
                    KApply ruleContents = (KApply) contents;
                    List<org.kframework.kore.K> items = ruleContents.klist().items();
                    switch (ruleContents.klabel().name()) {
                        case "#ruleNoConditions":
                            return Rule(items.get(0), _true, _true);
                        case "#ruleRequires":
                            return Rule(items.get(0), items.get(1), _true);
                        case "#ruleEnsures":
                            return Rule(items.get(0), _true, items.get(1));
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
