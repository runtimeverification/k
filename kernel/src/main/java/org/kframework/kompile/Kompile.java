// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.inject.Inject;
import org.kframework.Strategy;
import org.kframework.attributes.Source;
import org.kframework.backend.Backends;
import org.kframework.builtin.Sorts;
import org.kframework.compile.*;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckImports;
import org.kframework.compile.checks.CheckKLabels;
import org.kframework.compile.checks.CheckRHSVariables;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import java.io.File;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

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
        // these directories should be relative to the current working directory if we refer to them later after the WD has changed.
        kompileOptions.outerParsing.includes = lookupDirectories.stream().map(File::getAbsolutePath).collect(Collectors.toList());
        this.definitionParsing = new DefinitionParsing(
                lookupDirectories, kompileOptions.strict(), kem,
                parser, cacheParses, files.resolveKompiled("cache.bin"), !kompileOptions.outerParsing.noPrelude, kompileOptions.isKore());
        this.sw = sw;
    }

    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModuleName) {
        return run(definitionFile, mainModuleName, mainProgramsModuleName, defaultSteps(kompileOptions, kem, files, Collections.emptySet()));
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

        files.saveToKompiled("compiled.txt", kompiledDefinition.toString());
        sw.printIntermediate("Apply compile pipeline");

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(kompiledDefinition.mainModule());

        return new CompiledDefinition(kompileOptions, parsedDef, kompiledDefinition, files, kem, configInfo.getDefaultCell(configInfo.topCell()).klabel());
    }

    public Definition parseDefinition(File definitionFile, String mainModuleName, String mainProgramsModule) {
        return definitionParsing.parseDefinitionAndResolveBubbles(definitionFile, mainModuleName, mainProgramsModule);
    }

    private static Module filterStreamModules(Module input) {
        if (input.name().equals("STDIN-STREAM") || input.name().equals("STDOUT-STREAM")) {
            return Module(input.name(), Set(), Set(), input.att());
        }
        return input;
    }

    public static Definition resolveIOStreams(KExceptionManager kem,Definition d) {
        return DefinitionTransformer.from(new ResolveIOStreams(d, kem)::resolve, "resolving io streams")
                .andThen(DefinitionTransformer.from(Kompile::filterStreamModules, "resolving io streams"))
                .apply(d);
    }

    private static Module excludeModulesByTag(Set<String> excludedModuleTags, Module mod) {
        Set<Module> newImports = stream(mod.imports()).filter(_import -> excludedModuleTags.stream().noneMatch(tag -> _import.att().contains(tag))).collect(Collectors.toSet());
        return Module(mod.name(), immutable(newImports), mod.localSentences(), mod.att());
    }

    public static DefinitionTransformer excludeModulesByTag(Set<String> excludedModuleTags, Definition d) {
        return DefinitionTransformer.from(mod -> excludeModulesByTag(excludedModuleTags, mod), "remove modules based on attributes");
    }

    public static Function<Definition, Definition> defaultSteps(KompileOptions kompileOptions, KExceptionManager kem, FileUtil files, Set<String> excludedModuleTags) {
        DefinitionTransformer resolveStrict = DefinitionTransformer.from(new ResolveStrict(kompileOptions)::resolve, "resolving strict and seqstrict attributes");
        DefinitionTransformer resolveHeatCoolAttribute = DefinitionTransformer.fromSentenceTransformer(new ResolveHeatCoolAttribute(new HashSet<>(kompileOptions.transition))::resolve, "resolving heat and cool attributes");
        DefinitionTransformer resolveAnonVars = DefinitionTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolving \"_\" vars");
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve, "resolving semantic casts");
        DefinitionTransformer resolveFun = DefinitionTransformer.from(new ResolveFun()::resolve, "resolving #fun");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");
        DefinitionTransformer subsortKItem = DefinitionTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
        GenerateCoverage cov = new GenerateCoverage(kompileOptions.coverage, files);
        DefinitionTransformer genCoverage = DefinitionTransformer.fromRuleBodyTransformerWithRule(cov::gen, "generate coverage instrumentation");
        DefinitionTransformer numberSentences = DefinitionTransformer.fromSentenceTransformer(new NumberSentences()::number, "number sentences uniquely");

        return def -> excludeModulesByTag(excludedModuleTags, def)
                .andThen(d -> Kompile.resolveIOStreams(kem, d))
                .andThen(resolveFun)
                .andThen(resolveStrict)
                .andThen(resolveAnonVars)
                .andThen(d -> new ResolveContexts(kompileOptions).resolve(d))
                .andThen(numberSentences)
                .andThen(resolveHeatCoolAttribute)
                .andThen(resolveSemanticCasts)
                .andThen(generateSortPredicateSyntax)
                .andThen(Kompile::resolveFreshConstants)
                .andThen(AddImplicitComputationCell::transformDefinition)
                .andThen(new Strategy(kompileOptions.experimental.heatCoolStrategies).addStrategyCellToRulesTransformer())
                .andThen(ConcretizeCells::transformDefinition)
                .andThen(genCoverage)
                .andThen(d -> { cov.close(); return d; })
                .andThen(subsortKItem)
                .andThen(Kompile::addSemanticsModule)
                .apply(def);
    }

    public static Module subsortKItem(Module module) {
        java.util.Set<Sentence> prods = new HashSet<>();
        for (Sort srt : iterable(module.definedSorts())) {
            if (!RuleGrammarGenerator.isParserSort(srt)) {
                // KItem ::= Sort
                Production prod = Production(Sorts.KItem(), Seq(NonTerminal(srt)), Att());
                if (!module.sentences().contains(prod)) {
                    prods.add(prod);
                }
            }
        }
        if (prods.isEmpty()) {
            return module;
        } else {
            return Module(module.name(), module.imports(), Stream.concat(stream(module.localSentences()), prods.stream())
                    .collect(org.kframework.Collections.toSet()), module.att());
        }
    }

    public Rule parseAndCompileRule(CompiledDefinition compiledDef, String contents, Source source, Optional<Rule> parsedRule) {
        Rule parsed = parsedRule.orElse(parseRule(compiledDef, contents, source));
        return compileRule(compiledDef.kompiledDefinition, parsed);
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

        stream(parsedDef.modules()).forEach(m -> stream(m.localSentences()).forEach(new CheckRewrite(errors, m)::check));

        stream(parsedDef.modules()).forEach(new CheckImports(parsedDef.mainModule(), kem)::check);

        Set<String> moduleNames = new HashSet<>();
        stream(parsedDef.modules()).forEach(m -> {
            if (moduleNames.contains(m.name())) {
                errors.add(KEMException.compilerError("Found multiple modules with name: " + m.name()));
            }
            moduleNames.add(m.name());
        });

        CheckKLabels checkKLabels = new CheckKLabels(errors);
        // only check imported modules because otherwise we might have false positives
        Consumer<Module> checkModuleKLabels = m -> stream(m.localSentences()).forEach(s -> checkKLabels.check(s, m));
        stream(parsedDef.mainModule().importedModules()).forEach(checkModuleKLabels);
        checkModuleKLabels.accept(parsedDef.mainModule());

        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
            throw KEMException.compilerError("Had " + errors.size() + " structural errors.");
        }
    }

    public static Definition addSemanticsModule(Definition d) {
        java.util.Set<Module> allModules = mutable(d.modules());

        Module languageParsingModule = Constructors.Module("LANGUAGE-PARSING",
                Set(d.mainModule(),
                        d.getModule("K-TERM").get(),
                        d.getModule(RuleGrammarGenerator.ID_PROGRAM_PARSING).get()), Set(), Att());
        allModules.add(languageParsingModule);
        return Constructors.Definition(d.mainModule(), immutable(allModules), d.att());
    }

    public static Definition resolveFreshConstants(Definition input) {
        return DefinitionTransformer.from(new ResolveFreshConstants(input)::resolve, "resolving !Var variables")
                .apply(input);
    }

    public Rule compileRule(Definition compiledDef, Rule parsedRule) {
        return (Rule) UnaryOperator.<Sentence>identity()
                .andThen(new ResolveAnonVar()::resolve)
                .andThen(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve)
                .andThen(s -> concretizeSentence(s, compiledDef))
                .apply(parsedRule);
    }

    public Set<Module> parseModules(CompiledDefinition definition, String mainModule, File definitionFile) {
        return definitionParsing.parseModules(definition, mainModule, definitionFile);
    }

    private Sentence concretizeSentence(Sentence s, Definition input) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
        LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
        SortInfo sortInfo = SortInfo.fromModule(input.mainModule());
        return new ConcretizeCells(configInfo, labelInfo, sortInfo, input.mainModule()).concretize(s);
    }
}
