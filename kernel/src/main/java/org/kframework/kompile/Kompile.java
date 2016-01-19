// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import org.kframework.Strategy;
import org.kframework.attributes.Source;
import org.kframework.backend.Backends;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfo;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.definition.Constructors;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.kore.compile.AddImplicitComputationCell;
import org.kframework.kore.compile.ConcretizeCells;
import org.kframework.kore.compile.GenerateSortPredicateSyntax;
import org.kframework.kore.compile.ResolveAnonVar;
import org.kframework.kore.compile.ResolveContexts;
import org.kframework.kore.compile.ResolveFreshConstants;
import org.kframework.kore.compile.ResolveHeatCoolAttribute;
import org.kframework.kore.compile.ResolveIOStreams;
import org.kframework.kore.compile.ResolveSemanticCasts;
import org.kframework.kore.compile.ResolveStrict;
import org.kframework.kore.compile.SortInfo;
import org.kframework.kore.compile.checks.CheckConfigurationCells;
import org.kframework.kore.compile.checks.CheckRHSVariables;
import org.kframework.kore.compile.checks.CheckSortTopUniqueness;
import org.kframework.kore.compile.checks.CheckStreams;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static scala.compat.java8.JFunction.func;

/**
 * The new compilation pipeline. Everything is just wired together and will need clean-up once we deside on design.
 * Tracked by #1442.
 */
public class Kompile {
    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
    public static final String REQUIRE_PRELUDE_K = "requires \"prelude.k\"\n";

    public final KompileOptions kompileOptions;
    private final FileUtil files;
    private final KExceptionManager kem;
    private final ParserUtils parser;
    private final Stopwatch sw;
    private final DefinitionParsing definitionParsing;
    java.util.Set<KEMException> errors;

    public Kompile(KompileOptions kompileOptions, FileUtil files, KExceptionManager kem, Stopwatch sw, boolean cacheParses) {
        this(kompileOptions, kompileOptions.global, files, kem, sw, cacheParses);
    }

    public Kompile(KompileOptions kompileOptions, FileUtil files, KExceptionManager kem, boolean cacheParses) {
        this(kompileOptions, files, kem, new Stopwatch(kompileOptions.global), cacheParses);
    }

    public Kompile(KompileOptions kompileOptions, FileUtil files, KExceptionManager kem) {
        this(kompileOptions, files, kem, true);
    }

    @Inject
    public Kompile(KompileOptions kompileOptions, FileUtil files, KExceptionManager kem, Stopwatch sw) {
        this(kompileOptions, files, kem, sw, true);
    }

    public Kompile(KompileOptions kompileOptions, GlobalOptions global, FileUtil files, KExceptionManager kem, Stopwatch sw, boolean cacheParses) {
        this.kompileOptions = kompileOptions;
        this.files = files;
        this.kem = kem;
        this.errors = new HashSet<>();
        this.parser = new ParserUtils(files::resolveWorkingDirectory, kem, global);
        List<File> lookupDirectories = kompileOptions.outerParsing.includes.stream().map(files::resolveWorkingDirectory).collect(Collectors.toList());
        this.definitionParsing = new DefinitionParsing(
                lookupDirectories, kompileOptions.strict(), kem,
                parser, cacheParses, files.resolveKompiled("cache.bin"), !kompileOptions.outerParsing.noPrelude);
        this.sw = sw;
    }

    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModuleName) {
        return run(definitionFile, mainModuleName, mainProgramsModuleName, defaultSteps());
    }

    /**
     * Executes the Kompile tool. This tool accesses a
     *
     * @param definitionFile
     * @param mainModuleName
     * @param mainProgramsModuleName
     * @param programStartSymbol
     * @return
     */
    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModuleName, Function<Definition, Definition> pipeline) {
        Definition parsedDef = parseDefinition(definitionFile, mainModuleName, mainProgramsModuleName);
        sw.printIntermediate("Parse definition [" + definitionParsing.parsedBubbles.get() + "/" + (definitionParsing.parsedBubbles.get() + definitionParsing.cachedBubbles.get()) + " rules]");

        checkDefinition(parsedDef);

        Definition kompiledDefinition = pipeline.apply(parsedDef);
        sw.printIntermediate("Apply compile pipeline");

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(kompiledDefinition.mainModule());

        return new CompiledDefinition(kompileOptions, parsedDef, kompiledDefinition, configInfo.getDefaultCell(configInfo.topCell()).klabel());
    }

    public Definition parseDefinition(File definitionFile, String mainModuleName, String mainProgramsModule) {
        return definitionParsing.parseDefinitionAndResolveBubbles(definitionFile, mainModuleName, mainProgramsModule);
    }

    public Definition resolveIOStreams(Definition d) {
        return DefinitionTransformer.from(new ResolveIOStreams(d, kem)::resolve, "resolving io streams").apply(d);
    }

    public Function<Definition, Definition> defaultSteps() {
        DefinitionTransformer resolveStrict = DefinitionTransformer.from(new ResolveStrict(kompileOptions)::resolve, "resolving strict and seqstrict attributes");
        DefinitionTransformer resolveHeatCoolAttribute = DefinitionTransformer.fromSentenceTransformer(new ResolveHeatCoolAttribute(new HashSet<>(kompileOptions.transition))::resolve, "resolving heat and cool attributes");
        DefinitionTransformer resolveAnonVars = DefinitionTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolving \"_\" vars");
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve, "resolving semantic casts");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");

        return def -> func(this::resolveIOStreams)
                .andThen(resolveStrict)
                .andThen(resolveAnonVars)
                .andThen(func(d -> new ResolveContexts(kompileOptions).resolve(d)))
                .andThen(resolveHeatCoolAttribute)
                .andThen(resolveSemanticCasts)
                .andThen(generateSortPredicateSyntax)
                .andThen(func(this::resolveFreshConstants))
                .andThen(func(AddImplicitComputationCell::transformDefinition))
                .andThen(new Strategy(kompileOptions.experimental.heatCoolStrategies).addStrategyCellToRulesTransformer())
                .andThen(func(ConcretizeCells::transformDefinition))
                .andThen(func(this::addSemanticsModule))
                .apply(def);
    }

    public Rule parseAndCompileRule(CompiledDefinition compiledDef, String contents, Source source, Optional<Rule> parsedRule) {
        Rule parsed = parsedRule.orElse(parseRule(compiledDef, contents, source));
        return compileRule(compiledDef, parsed);
    }

    public Rule parseRule(CompiledDefinition compiledDef, String contents, Source source) {
        return definitionParsing.parseRule(compiledDef, contents, source);
    }

    private void checkDefinition(Definition parsedDef) {
        CheckRHSVariables checkRHSVariables = new CheckRHSVariables(errors);
        stream(parsedDef.modules()).forEach(m -> stream(m.localSentences()).forEach(checkRHSVariables::check));

        stream(parsedDef.modules()).forEach(m -> stream(m.localSentences()).forEach(new CheckConfigurationCells(errors, m)::check));

        stream(parsedDef.modules()).forEach(m -> stream(m.localSentences()).forEach(new CheckSortTopUniqueness(errors, m)::check));

        stream(parsedDef.modules()).forEach(m -> stream(m.localSentences()).forEach(new CheckStreams(errors, m)::check));

        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
            throw KEMException.compilerError("Had " + errors.size() + " structural errors.");
        }
    }

    public Definition addSemanticsModule(Definition d) {
        java.util.Set<Sentence> prods = new HashSet<>();
        for (Sort srt : iterable(d.mainModule().definedSorts())) {
            if (!RuleGrammarGenerator.isParserSort(srt)) {
                // KItem ::= Sort
                prods.add(Production(Sorts.KItem(), Seq(NonTerminal(srt)), Att()));
            }
        }
        Module withKSeq = Constructors.Module("SEMANTICS", Set(d.mainModule()), immutable(prods), Att());
        java.util.Set<Module> allModules = mutable(d.modules());
        allModules.add(withKSeq);

        Module languageParsingModule = Constructors.Module("LANGUAGE-PARSING",
                Set(d.mainModule(),
                        d.getModule("K-TERM").get(),
                        d.getModule(RuleGrammarGenerator.ID_PROGRAM_PARSING).get()), Set(), Att());
        allModules.add(languageParsingModule);
        return Constructors.Definition(withKSeq, immutable(allModules), d.att());
    }

    public Definition resolveFreshConstants(Definition input) {
        return DefinitionTransformer.from(new ResolveFreshConstants(input)::resolve, "resolving !Var variables")
                .apply(input);
    }

    public Rule compileRule(CompiledDefinition compiledDef, Rule parsedRule) {
        return (Rule) func(new ResolveAnonVar()::resolve)
                .andThen(func(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve))
                .andThen(func(s -> concretizeSentence(s, compiledDef.kompiledDefinition)))
                .apply(parsedRule);
    }

    public Module parseModule(CompiledDefinition definition, File definitionFile) {
        return definitionParsing.parseModule(definition, definitionFile, !kompileOptions.outerParsing.noPrelude);
    }

    private Sentence concretizeSentence(Sentence s, Definition input) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
        LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
        SortInfo sortInfo = SortInfo.fromModule(input.mainModule());
        return new ConcretizeCells(configInfo, labelInfo, sortInfo, input.mainModule()).concretize(s);
    }
}
