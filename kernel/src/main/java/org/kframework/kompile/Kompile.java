// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.inject.Inject;
import org.apache.commons.collections15.ListUtils;
import org.kframework.Collections;
import org.kframework.attributes.Source;
import org.kframework.backend.Backends;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfo;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.definition.Bubble;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.Sort;
import org.kframework.kore.compile.*;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.ParseCache;
import org.kframework.parser.concrete2kore.ParseCache.ParsedSentence;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import scala.Tuple2;
import scala.collection.Set;
import scala.util.Either;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;
import static scala.compat.java8.JFunction.*;

/**
 * The new compilation pipeline. Everything is just wired together and will need clean-up once we deside on design.
 * Tracked by #1442.
 */

public class Kompile {

    public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
    public static final String REQUIRE_PRELUDE_K = "requires \"prelude.k\"\n";
    public static final Sort START_SYMBOL = Sort("RuleContent");

    public final KompileOptions kompileOptions;

    private final FileUtil files;
    private final KExceptionManager kem;
    private final ParserUtils parser;
    private final boolean cacheParses;
    private final BinaryLoader loader;
    private final Stopwatch sw;

    private final AtomicInteger parsedBubbles = new AtomicInteger(0);
    private final AtomicInteger cachedBubbles = new AtomicInteger(0);

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
        this.parser = new ParserUtils(files, kem, global);
        this.cacheParses = cacheParses;
        this.loader = new BinaryLoader(kem);
        this.sw = sw;
    }


    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModuleName, Sort programStartSymbol) {
        return run(definitionFile, mainModuleName, mainProgramsModuleName, programStartSymbol, defaultSteps());
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
    public CompiledDefinition run(File definitionFile, String mainModuleName, String mainProgramsModuleName, Sort programStartSymbol, Function<Definition, Definition> pipeline) {
        Definition parsedDef = parseDefinition(definitionFile, mainModuleName, mainProgramsModuleName, true);
        sw.printIntermediate("Parse definition [" + parsedBubbles.get() + "/" + (parsedBubbles.get() + cachedBubbles.get()) + " rules]");

        Definition kompiledDefinition = pipeline.apply(parsedDef);
        sw.printIntermediate("Apply compile pipeline");

        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(kompiledDefinition.mainModule());

        return new CompiledDefinition(kompileOptions, parsedDef, kompiledDefinition, programStartSymbol, configInfo.getDefaultCell(configInfo.topCell()).klabel());
    }

    public Function<Definition, Definition> defaultSteps() {
        DefinitionTransformer resolveStrict = DefinitionTransformer.from(new ResolveStrict(kompileOptions)::resolve, "resolving strict and seqstrict attributes");
        DefinitionTransformer resolveContexts = DefinitionTransformer.from(new ResolveContexts(kompileOptions)::resolve, "resolving context sentences");
        DefinitionTransformer resolveHeatCoolAttribute = DefinitionTransformer.fromSentenceTransformer(new ResolveHeatCoolAttribute()::resolve, "resolving heat and cool attributes");
        DefinitionTransformer resolveAnonVars = DefinitionTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolving \"_\" vars");
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve, "resolving semantic casts");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");

        return def -> func(this::resolveIOStreams)
                .andThen(resolveStrict)
                .andThen(resolveAnonVars)
                .andThen(resolveContexts)
                .andThen(resolveHeatCoolAttribute)
                .andThen(resolveSemanticCasts)
                .andThen(generateSortPredicateSyntax)
                .andThen(func(this::resolveFreshConstants))
                .andThen(func(AddImplicitComputationCell::transformDefinition))
                .andThen(func(ConcretizeCells::transformDefinition))
                .andThen(func(this::addSemanticsModule))
                .andThen(func(this::addProgramModule))
                .apply(def);
    }

    public Definition resolveIOStreams(Definition d) {
        return DefinitionTransformer.from(new ResolveIOStreams(d)::resolve, "resolving io streams").apply(d);
    }

    public Definition addSemanticsModule(Definition d) {
        java.util.Set<Sentence> prods = new HashSet<>();
        for (Sort srt : iterable(d.mainModule().definedSorts())) {
            if (!RuleGrammarGenerator.isParserSort(srt)) {
                // KItem ::= Sort
                prods.add(Production(Sorts.KItem(), Seq(NonTerminal(srt)), Att()));
            }
        }
        Module withKSeq = Module("SEMANTICS", Set(d.mainModule()), immutable(prods), Att());
        java.util.Set<Module> allModules = mutable(d.modules());
        allModules.add(withKSeq);

        Module languageParsingModule = Module("LANGUAGE-PARSING",
                Set(d.mainModule(),
                        d.mainSyntaxModule(),
                        d.getModule("K-TERM").get()), Set(), Att());
        allModules.add(languageParsingModule);
        return Definition(withKSeq, d.mainSyntaxModule(), immutable(allModules));
    }

    public Definition resolveFreshConstants(Definition input) {
        return DefinitionTransformer.from(new ResolveFreshConstants(input)::resolve, "resolving !Var variables")
                .apply(input);
    }

    public Definition addProgramModule(Definition d) {
        Module programsModule = gen.getProgramsGrammar(d.mainSyntaxModule());
        java.util.Set<Module> allModules = mutable(d.modules());
        allModules.add(programsModule);
        return Definition(d.mainModule(), programsModule, immutable(allModules));
    }

    private Sentence concretizeSentence(Sentence s, Definition input) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
        LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
        SortInfo sortInfo = SortInfo.fromModule(input.mainModule());
        return new ConcretizeCells(configInfo, labelInfo, sortInfo).concretize(s);
    }

    public Module parseModule(CompiledDefinition definition, File definitionFile, boolean dropQuote) {
        java.util.Set<Module> modules = parser.loadModules(
                mutable(definition.getParsedDefinition().modules()),
                "require " + StringUtil.enquoteCString(definitionFile.getPath()),
                definitionFile,
                definitionFile.getParentFile(),
                Lists.newArrayList(BUILTIN_DIRECTORY),
                dropQuote);

        if (modules.size() != 1) {
            throw KEMException.compilerError("Expected to find a file with 1 module: found " + modules.size() + " instead.");
        }

        Module module = modules.iterator().next();

        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        caches = new HashMap<>();

        if (cacheParses) {
            try {
                caches = loader.load(Map.class, files.resolveKompiled("cache.bin"));
            } catch (FileNotFoundException e) {
            } catch (IOException | ClassNotFoundException e) {
                kem.registerInternalHiddenWarning("Invalidating serialized cache due to corruption.", e);
            }
        }

        gen = new RuleGrammarGenerator(definition.getParsedDefinition(), kompileOptions.strict());
        Module modWithConfig = resolveConfig(module, definition.getParsedDefinition());

        gen = new RuleGrammarGenerator(definition.getParsedDefinition(), kompileOptions.strict());
        Module parsedMod = resolveBubbles(modWithConfig);

        if (cacheParses) {
            loader.saveOrDie(files.resolveKompiled("cache.bin"), caches);
        }
        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.getKException()).collect(Collectors.toList()));
            throw KEMException.compilerError("Had " + errors.size() + " parsing errors.");
        }
        return parsedMod;
    }

    public Definition parseDefinition(File definitionFile, String mainModuleName, String mainProgramsModule, boolean dropQuote) {
        String prelude = REQUIRE_PRELUDE_K;
        if (kompileOptions.noPrelude) {
            prelude = "";
        }
        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, prelude + FileUtil.load(definitionFile),
                definitionFile,
                definitionFile.getParentFile(),
                ListUtils.union(kompileOptions.includes.stream()
                                .map(files::resolveWorkingDirectory).collect(Collectors.toList()),
                        Lists.newArrayList(BUILTIN_DIRECTORY)),
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
                    java.util.Set<Module> imports = mutable(mod.imports());
                    imports.add(definition.getModule("DEFAULT-CONFIGURATION").get());
                    return Module(mod.name(), (Set<Module>) immutable(imports), mod.localSentences(), mod.att());
                }
                return mod;
            }, "adding default configuration").apply(definition);
        } else {
            definitionWithConfigBubble = definition;
        }

        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        caches = new HashMap<>();

        if (cacheParses) {
            try {
                caches = loader.load(Map.class, files.resolveKompiled("cache.bin"));
            } catch (FileNotFoundException e) {
            } catch (IOException | ClassNotFoundException e) {
                kem.registerInternalHiddenWarning("Invalidating serialized cache due to corruption.", e);
            }
        }

        gen = new RuleGrammarGenerator(definitionWithConfigBubble, kompileOptions.strict());
        Definition defWithConfig = DefinitionTransformer.from(m -> resolveConfig(m, definitionWithConfigBubble), "parsing configurations").apply(definitionWithConfigBubble);

        gen = new RuleGrammarGenerator(defWithConfig, kompileOptions.strict());
        Definition parsedDef = DefinitionTransformer.from(this::resolveBubbles, "parsing rules").apply(defWithConfig);

        if (cacheParses) {
            loader.saveOrDie(files.resolveKompiled("cache.bin"), caches);
        }
        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.getKException()).collect(Collectors.toList()));
            throw KEMException.compilerError("Had " + errors.size() + " parsing errors.");
        }
        return parsedDef;
    }

    Map<String, ParseCache> caches;
    java.util.Set<ParseFailedException> errors;
    RuleGrammarGenerator gen;

    private Module resolveConfig(Module module, Definition def) {
        if (stream(module.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config")).count() == 0)
            return module;
        Module configParserModule = gen.getConfigGrammar(module);

        ParseCache cache = loadCache(configParserModule);
        ParseInModule parser = gen.getCombinedGrammar(cache.getModule());

        Set<Sentence> configDeclProductions = stream(module.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("config"))
                .flatMap(b -> performParse(cache.getCache(), parser, b))
                .map(contents -> {
                    KApply configContents = (KApply) contents;
                    List<K> items = configContents.klist().items();
                    switch (configContents.klabel().name()) {
                    case "#ruleNoConditions":
                        return Configuration(items.get(0), BooleanUtils.TRUE, configContents.att());
                    case "#ruleEnsures":
                        return Configuration(items.get(0), items.get(1), configContents.att());
                    default:
                        throw KEMException.compilerError("Illegal configuration with requires clause detected.", configContents);
                    }
                })
                .flatMap(
                        configDecl -> stream(GenerateSentencesFromConfigDecl.gen(configDecl.body(), configDecl.ensures(), configDecl.att(), parser.getExtensionModule())))
                .collect(Collections.toSet());

        Module mapModule;
        if (def.getModule("MAP").isDefined()) {
            mapModule = def.getModule("MAP").get();
        } else {
            throw KEMException.compilerError("Module Map must be visible at the configuration declaration, in module " + module.name());
        }
        return Module(module.name(), (Set<Module>) module.imports().$bar(Set(mapModule)), (Set<Sentence>) module.localSentences().$bar(configDeclProductions), module.att());
    }

    private Module resolveBubbles(Module module) {
        if (stream(module.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> !b.sentenceType().equals("config")).count() == 0)
            return module;
        Module ruleParserModule = gen.getRuleGrammar(module);

        ParseCache cache = loadCache(ruleParserModule);
        ParseInModule parser = gen.getCombinedGrammar(cache.getModule());

        Set<Sentence> ruleSet = stream(module.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("rule"))
                .flatMap(b -> performParse(cache.getCache(), parser, b))
                .map(this::upRule)
                .collect(Collections.toSet());

        Set<Sentence> contextSet = stream(module.localSentences())
                .parallel()
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals("context"))
                .flatMap(b -> performParse(cache.getCache(), parser, b))
                .map(this::upContext)
                .collect(Collections.toSet());

        return Module(module.name(), module.imports(),
                stream((Set<Sentence>) module.localSentences().$bar(ruleSet).$bar(contextSet)).filter(b -> !(b instanceof Bubble)).collect(Collections.toSet()), module.att());
    }

    public Rule parseRule(CompiledDefinition compiledDef, String contents, Source source) {
        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        gen = new RuleGrammarGenerator(compiledDef.kompiledDefinition, kompileOptions.strict());
        java.util.Set<K> res = performParse(new HashMap<>(), gen.getCombinedGrammar(gen.getRuleGrammar(compiledDef.executionModule())),
                new Bubble("rule", contents, Att().add("contentStartLine", 1).add("contentStartColumn", 1).add("Source", source.source())))
                .collect(Collectors.toSet());
        if (!errors.isEmpty()) {
            throw errors.iterator().next();
        }
        return upRule(res.iterator().next());
    }

    public Rule compileRule(CompiledDefinition compiledDef, Rule parsedRule) {
        return (Rule) func(new ResolveAnonVar()::resolve)
                .andThen(func(new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA))::resolve))
                .andThen(func(s -> concretizeSentence(s, compiledDef.kompiledDefinition)))
                .apply(parsedRule);
    }

    public Rule parseAndCompileRule(CompiledDefinition compiledDef, String contents, Source source, Optional<Rule> parsedRule) {
        Rule parsed = parsedRule.orElse(parseRule(compiledDef, contents, source));
        return compileRule(compiledDef, parsed);
    }

    private Rule upRule(K contents) {
        KApply ruleContents = (KApply) contents;
        List<org.kframework.kore.K> items = ruleContents.klist().items();
        switch (ruleContents.klabel().name()) {
        case "#ruleNoConditions":
            return Rule(items.get(0), BooleanUtils.TRUE, BooleanUtils.TRUE, ruleContents.att());
        case "#ruleRequires":
            return Rule(items.get(0), items.get(1), BooleanUtils.TRUE, ruleContents.att());
        case "#ruleEnsures":
            return Rule(items.get(0), BooleanUtils.TRUE, items.get(1), ruleContents.att());
        case "#ruleRequiresEnsures":
            return Rule(items.get(0), items.get(1), items.get(2), ruleContents.att());
        default:
            throw new AssertionError("Wrong KLabel for rule content");
        }
    }

    private Context upContext(K contents) {
        KApply ruleContents = (KApply) contents;
        List<K> items = ruleContents.klist().items();
        switch (ruleContents.klabel().name()) {
        case "#ruleNoConditions":
            return Context(items.get(0), BooleanUtils.TRUE, ruleContents.att());
        case "#ruleRequires":
            return Context(items.get(0), items.get(1), ruleContents.att());
        default:
            throw KEMException.criticalError("Illegal context with ensures clause detected.", contents);
        }
    }

    private ParseCache loadCache(Module parser) {
        ParseCache cachedParser = caches.get(parser.name());
        if (cachedParser == null || !equalsSyntax(cachedParser.getModule(), parser) || cachedParser.isStrict() != kompileOptions.strict()) {
            cachedParser = new ParseCache(parser, kompileOptions.strict(), java.util.Collections.synchronizedMap(new HashMap<>()));
            caches.put(parser.name(), cachedParser);
        }
        return cachedParser;
    }

    private boolean equalsSyntax(Module _this, Module that) {
        if (!_this.productions().equals(that.productions())) return false;
        if (!_this.priorities().equals(that.priorities())) return false;
        if (!_this.leftAssoc().equals(that.leftAssoc())) return false;
        if (!_this.rightAssoc().equals(that.rightAssoc())) return false;
        return _this.sortDeclarations().equals(that.sortDeclarations());
    }

    private Stream<? extends K> performParse(Map<String, ParsedSentence> cache, ParseInModule parser, Bubble b) {
        int startLine = b.att().<Integer>get("contentStartLine").get();
        int startColumn = b.att().<Integer>get("contentStartColumn").get();
        String source = b.att().<String>get("Source").get();
        Tuple2<Either<java.util.Set<ParseFailedException>, K>, java.util.Set<ParseFailedException>> result;
        if (cache.containsKey(b.contents())) {
            ParsedSentence parse = cache.get(b.contents());
            cachedBubbles.getAndIncrement();
            kem.addAllKException(parse.getWarnings().stream().map(e -> e.getKException()).collect(Collectors.toList()));
            return Stream.of(parse.getParse());
        } else {
            result = parser.parseString(b.contents(), START_SYMBOL, Source.apply(source), startLine, startColumn);
            parsedBubbles.getAndIncrement();
            kem.addAllKException(result._2().stream().map(e -> e.getKException()).collect(Collectors.toList()));
            if (result._1().isRight()) {
                KApply k = (KApply) TreeNodesToKORE.down(result._1().right().get());
                k = KApply(k.klabel(), k.klist(), k.att().addAll(b.att().remove("contentStartLine").remove("contentStartColumn").remove("Source").remove("Location")));
                cache.put(b.contents(), new ParsedSentence(k, new HashSet<>(result._2())));
                return Stream.of(k);
            } else {
                errors.addAll(result._1().left().get());
                return Stream.empty();
            }
        }
    }
}
