// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import org.apache.commons.collections15.ListUtils;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.GenerateSentencesFromConfigDecl;
import org.kframework.definition.Bubble;
import org.kframework.definition.Claim;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Import;
import org.kframework.kore.AddAtt;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.Sort;
import org.kframework.parser.ParserUtils;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.inner.ParseCache;
import org.kframework.parser.inner.ParseCache.ParsedSentence;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.generator.RuleGrammarGenerator;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Option;
import scala.Tuple2;
import scala.collection.Set;
import scala.collection.mutable.LinkedHashSet;
import scala.util.Either;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * A bundle of code doing various aspects of definition parsing.
 * TODO: In major need of refactoring.
 * @cos refactored this code out of Kompile but none (or close to none) of it was originally written by him.
 */
public class DefinitionParsing {
    public static final Sort START_SYMBOL = Sorts.RuleContent();
    private static final String rule = "rule";
    private static final String claim = "claim";
    private static final String configuration = "config";
    private static final String alias = "alias";
    private static final String context = "context";
    private final File cacheFile;
    private final boolean autoImportDomains;
    private final boolean kore;
    private final KompileOptions options;

    private final KExceptionManager kem;
    private final FileUtil files;
    private final ParserUtils parser;
    private final boolean cacheParses;
    private final BinaryLoader loader;
    private final Stopwatch sw;

    public final AtomicInteger parsedBubbles = new AtomicInteger(0);
    public final AtomicInteger cachedBubbles = new AtomicInteger(0);
    private final boolean isStrict;
    private final boolean profileRules;
    private final List<File> lookupDirectories;

    public DefinitionParsing(
            List<File> lookupDirectories,
            KompileOptions options,
            KExceptionManager kem,
            FileUtil files,
            ParserUtils parser,
            boolean cacheParses,
            File cacheFile,
            Stopwatch sw) {
        this.lookupDirectories = lookupDirectories;
        this.options = options;
        this.kem = kem;
        this.files = files;
        this.parser = parser;
        this.cacheParses = cacheParses;
        this.cacheFile = cacheFile;
        this.autoImportDomains = !options.outerParsing.noPrelude;
        this.kore = options.isKore();
        this.loader = new BinaryLoader(this.kem);
        this.isStrict = options.strict();
        this.profileRules = options.profileRules;
        this.sw = sw;
    }

    public java.util.Set<Module> parseModules(CompiledDefinition definition, String mainModule, String entryPointModule, File definitionFile, java.util.Set<String> excludeModules, boolean readOnlyCache) {
        Definition def = parser.loadDefinition(
                mainModule,
                mutable(definition.getParsedDefinition().modules()),
                FileUtil.load(definitionFile),
                Source.apply(definitionFile.getAbsolutePath()),
                definitionFile.getParentFile(),
                ListUtils.union(Lists.newArrayList(Kompile.BUILTIN_DIRECTORY),
                  lookupDirectories),
                kore,
                options.preprocess,
                options.bisonLists);

        if (!def.getModule(mainModule).isDefined()) {
          throw KEMException.criticalError("Module " + mainModule + " does not exist.");
        }
        if (!def.getModule(entryPointModule).isDefined()) {
          throw KEMException.criticalError("Module " + entryPointModule + " does not exist.");
        }
        Stream<Module> modules = Stream.of(def.getModule(mainModule).get());
        modules = Stream.concat(modules, stream(def.getModule(mainModule).get().importedModules()));
        modules = Stream.concat(modules, Stream.of(def.getModule(entryPointModule).get()));
        modules = Stream.concat(modules, stream(def.getModule(entryPointModule).get().importedModules()));
        modules = Stream.concat(modules,
                stream(def.entryModules()).filter(m -> !stream(m.sentences()).anyMatch(s -> s instanceof Bubble)));
        def = Definition(def.mainModule(), modules.collect(Collections.toSet()), def.att());

        def = Kompile.excludeModulesByTag(excludeModules).apply(def);

        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        caches = loadCaches();

        gen = new RuleGrammarGenerator(def);

        try {
          def = resolveConfigBubbles(def, gen);
        } catch (KEMException e) {
            errors.add(e);
            throwExceptionIfThereAreErrors();
            throw new AssertionError("should not reach this statement");
        }

        def = resolveNonConfigBubbles(def);
        if (! readOnlyCache) {
            saveCachesAndReportParsingErrors();
        }
        return mutable(def.entryModules());
    }

    public Map<String, ParseCache> loadCaches() {
        Map<String, ParseCache> result;
        //noinspection unchecked
        result = cacheParses ? loader.loadCache(Map.class, cacheFile) : null;
        if (result == null) {
            result = new HashMap<>();
        }
        return result;
    }

    private void saveCachesAndReportParsingErrors() {
        saveCaches();
        throwExceptionIfThereAreErrors();
    }

    private void saveCaches() {
        if (cacheParses) {
            loader.saveOrDie(cacheFile, caches);
        }
    }

    public Definition parseDefinitionAndResolveBubbles(File definitionFile, String mainModuleName, String mainProgramsModule, java.util.Set<String> excludedModuleTags) {
        Definition parsedDefinition = parseDefinition(definitionFile, mainModuleName, mainProgramsModule);
        Stream<Module> modules = Stream.of(parsedDefinition.mainModule());
        modules = Stream.concat(modules, stream(parsedDefinition.mainModule().importedModules()));
        Option<Module> syntaxModule = parsedDefinition.getModule(mainProgramsModule);
        if (syntaxModule.isDefined()) {
            modules = Stream.concat(modules, Stream.of(syntaxModule.get()));
            modules = Stream.concat(modules, stream(syntaxModule.get().importedModules()));
        }
        modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("K-REFLECTION").get()));
        modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("STDIN-STREAM").get()));
        modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("STDOUT-STREAM").get()));
        modules = Stream.concat(modules,
                stream(parsedDefinition.entryModules()).filter(m -> !stream(m.sentences()).anyMatch(s -> s instanceof Bubble)));
        Definition trimmed = Definition(parsedDefinition.mainModule(), modules.collect(Collections.toSet()),
                parsedDefinition.att());
        trimmed = Kompile.excludeModulesByTag(excludedModuleTags).apply(trimmed);
        sw.printIntermediate("Outer parsing [" + trimmed.entryModules().size() + " modules]");
        Definition afterResolvingConfigBubbles = resolveConfigBubbles(trimmed, parsedDefinition.getModule("DEFAULT-CONFIGURATION").get(), parsedDefinition.getModule("MAP").get());
        sw.printIntermediate("Parse configurations [" + parsedBubbles.get() + "/" + (parsedBubbles.get() + cachedBubbles.get()) + " declarations]");
        parsedBubbles.set(0);
        cachedBubbles.set(0);
        Definition afterResolvingAllOtherBubbles = resolveNonConfigBubbles(afterResolvingConfigBubbles);
        saveCachesAndReportParsingErrors();
        return afterResolvingAllOtherBubbles;
    }

    private void throwExceptionIfThereAreErrors() {
        if (!errors.isEmpty()) {
            kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
            throw KEMException.compilerError("Had " + errors.size() + " parsing errors.");
        }
    }

    public Definition parseDefinition(File definitionFile, String mainModuleName, String mainProgramsModule) {
        Definition definition = parser.loadDefinition(
                mainModuleName,
                mainProgramsModule, FileUtil.load(definitionFile),
                definitionFile,
                definitionFile.getParentFile(),
                ListUtils.union(lookupDirectories,
                        Lists.newArrayList(Kompile.BUILTIN_DIRECTORY)),
                autoImportDomains,
                kore,
                options.preprocess,
                options.bisonLists);
        Module m = definition.mainModule();
        return options.coverage ? DefinitionTransformer.from(mod -> mod.equals(m) ? Module(m.name(), (Set<Module>)m.imports().$bar(Set(definition.getModule("K-IO").get())), m.localSentences(), m.att()) : mod, "add implicit modules").apply(definition) : definition;
    }

    protected Definition resolveConfigBubbles(Definition definition, Module defaultConfiguration, Module mapModule) {
        boolean hasConfigDecl = stream(definition.mainModule().sentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals(configuration))
                .findFirst().isPresent();

        Definition definitionWithConfigBubble = DefinitionTransformer.from(mod -> {
            if (mod.equals(definition.mainModule())) {
                java.util.Set<Module> imports = mutable(mod.imports());
                if (!hasConfigDecl) {
                    imports.add(defaultConfiguration);
                }
                imports.add(mapModule);
                return Module(mod.name(), (Set<Module>) immutable(imports), mod.localSentences(), mod.att());
            }
            return mod;
        }, "adding default configuration").apply(definition);

        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        caches = loadCaches();

        gen = new RuleGrammarGenerator(definitionWithConfigBubble);

        Definition result;
        try {
            result = resolveConfigBubbles(definitionWithConfigBubble, gen);
        } catch (KEMException e) {
            errors.add(e);
            throwExceptionIfThereAreErrors();
            throw new AssertionError("should not reach this statement");
        }
        throwExceptionIfThereAreErrors();
        return result;
    }

    Map<String, ParseCache> caches;
    private java.util.Set<KEMException> errors;
    RuleGrammarGenerator gen;

    public java.util.Set<KEMException> errors() {
        return errors;
    }

    private Definition resolveConfigBubbles(Definition def, RuleGrammarGenerator gen) {
      return DefinitionTransformer.from(m -> resolveConfigBubbles(def, m, gen), "parsing configs").apply(def);
    }

    private Module resolveConfigBubbles(Definition def, Module inputModule, RuleGrammarGenerator gen) {
        if (stream(inputModule.localSentences())
                .filter(s -> s instanceof Bubble)
                .map(b -> (Bubble) b)
                .filter(b -> b.sentenceType().equals(configuration)).count() == 0)
            return inputModule;


        Set<Sentence> importedConfigurationSortsSubsortedToCell = stream(inputModule.productions())
                .filter(p -> p.att().contains("cell"))
                .map(p -> Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort())))).collect(Collections.toSet());

        Module module = Module(inputModule.name(), (Set<Module>) inputModule.imports(),
                (Set<Sentence>) inputModule.localSentences().$bar(importedConfigurationSortsSubsortedToCell),
                inputModule.att());

        Set<Sentence> configDeclProductions;
        ParseCache cache = loadCache(gen.getConfigGrammar(module));
        try (ParseInModule parser = RuleGrammarGenerator.getCombinedGrammar(cache.getModule(), isStrict, profileRules, files)) {
             parser.getScanner(options.global);
             configDeclProductions = stream(module.localSentences())
                    .parallel()
                    .filter(s -> s instanceof Bubble)
                    .map(b -> (Bubble) b)
                    .filter(b -> b.sentenceType().equals(configuration))
                    .flatMap(b -> performParse(cache.getCache(), parser, parser.getScanner(), b))
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
                            configDecl -> stream(GenerateSentencesFromConfigDecl.gen(configDecl.body(), configDecl.ensures(), configDecl.att(), parser.getExtensionModule(), kore)))
                    .collect(Collections.toSet());
        }

        Set<Sentence> configDeclSyntax = stream(configDeclProductions).filter(Sentence::isSyntax).collect(Collections.toSet());
        Set<Sentence> configDeclRules = stream(configDeclProductions).filter(Sentence::isNonSyntax).collect(Collections.toSet());

        if (module.name().endsWith(Import.IMPORTS_SYNTAX_SUFFIX)) {
            Module mapModule;
            if (def.getModule("MAP$SYNTAX").isDefined()) {
                mapModule = def.getModule("MAP$SYNTAX").get();
            } else {
                throw KEMException.compilerError("Module Map must be visible at the configuration declaration, in module " + module.name());
            }
            return Module(module.name(), (Set<Module>) module.imports().$bar(Set(mapModule)),
                    (Set<Sentence>) module.localSentences().$bar(configDeclSyntax).filter(s -> !(s instanceof Bubble && ((Bubble) s).sentenceType().equals(configuration))),
                    module.att());
        } else {
            Module mapModule;
            if (def.getModule("MAP").isDefined()) {
                mapModule = def.getModule("MAP").get();
            } else {
                throw KEMException.compilerError("Module Map must be visible at the configuration declaration, in module " + module.name());
            }
            return Module(module.name(), (Set<Module>) module.imports().$bar(Set(mapModule)),
                    (Set<Sentence>) module.localSentences().$bar(configDeclRules).filter(s -> !(s instanceof Bubble && ((Bubble) s).sentenceType().equals(configuration))),
                    module.att());
        }

    }

    // Find the entry modules (not included in any other module)
    private static java.util.Set<Module> getBotModules(Set<Module> allModules) {
        java.util.Set<Module> included = new HashSet<>();
        for (Module m : mutable(allModules)) {
            included.addAll(mutable(m.importedModules()));
        }
        java.util.Set<Module> rez = mutable(allModules);
        rez.removeAll(included);
        return rez;
    }

    public Definition resolveNonConfigBubbles(Definition defWithConfig) {
        RuleGrammarGenerator gen = new RuleGrammarGenerator(defWithConfig);
        // load cached bubbles
        Definition defWithCaches = DefinitionTransformer.from(m -> {
            if (stream(m.localSentences()).noneMatch(s -> s instanceof Bubble))
                return m;
            ParseCache cache = loadCache(gen.getRuleGrammar(m));
            java.util.Set<Sentence> replacedBubbles = new HashSet<>();
            java.util.Set<Sentence> cachedParses = new HashSet<>();
            for (Sentence s : mutable(m.localSentences())) {
                if (!(s instanceof Bubble))
                    continue;
                Bubble b = ((Bubble) s);
                if (cache.getCache().containsKey(b.contents())) {
                    replacedBubbles.add(b);
                    ParsedSentence parsed = cache.getCache().get(b.contents());
                    cachedBubbles.getAndIncrement();
                    if (kem.options.warnings2errors) {
                        for (KEMException err : parsed.getWarnings().stream().map(e -> (KEMException) e).collect(Collectors.toList())) {
                            if (kem.options.includesExceptionType(err.exception.getType())) {
                                errors.add(KEMException.asError(err));
                            }
                        }
                    } else {
                        kem.addAllKException(parsed.getWarnings().stream().map(e -> e.getKException()).collect(Collectors.toList()));
                    }
                    // TODO: update error location #1873
                    Att att = parsed.getParse().att().addAll(b.att().remove("contentStartLine").remove("contentStartColumn").remove(Source.class).remove(Location.class));
                    cachedParses.add(upSentence(new AddAtt(a -> att).apply(parsed.getParse()), b.sentenceType()));
                    // TODO: check to see if we don't parse the same rules twice because of module duplication!!!!!!!!!!!!!!!!!
                }
            }
            if (!replacedBubbles.isEmpty()) {
                // make a new module with replaced bubbles
                return Module(m.name(),
                        m.imports(),
                        stream((Set<Sentence>) m.localSentences().$minus$minus(immutable(replacedBubbles)).
                                                                  $bar(immutable(cachedParses))).collect(Collections.toSet()),
                        m.att());
            }
            return m;
        }, "").apply(defWithConfig);
        // prepare scanners for remaining bubbles
        // scanners can be reused so find the bottom modules which include all other modules
        java.util.Set<Module> botMods = getBotModules(defWithCaches.modules()).stream().filter(m -> m.sentences().filter(s -> s instanceof Bubble).size() != 0).collect(Collectors.toSet());
        // prefer modules that import the main module. This way we avoid using the main syntax module which could contain problematic syntax for rule parsing
        java.util.Set<Module> orderedBotMods = new java.util.LinkedHashSet<>();
        for (Module m : botMods) {
            if (m.name().equals(defWithCaches.mainModule().name()) || m.importedModuleNames().contains(defWithCaches.mainModule().name()))
                orderedBotMods.add(m);
        }
        orderedBotMods.addAll(botMods);

        // map the module name to the scanner that it should use when parsing
        java.util.Map<String, Module> donorModule = new HashMap<>();
        for (Module m : mutable(defWithCaches.modules())) {
            if (stream(m.localSentences()).anyMatch(s -> s instanceof Bubble)) {
                Module scannerModule = orderedBotMods.stream().filter(bm -> m.equals(bm) || bm.importedModuleNames().contains(m.name())).findFirst()
                        .orElseThrow(() -> new AssertionError("Expected at least one bottom module to have a suitable scanner: " + m.name()));
                donorModule.put(m.name(), scannerModule);
            }
        }
        // create scanners
        Map<Module, ParseInModule> donorScanners = new HashSet<>(donorModule.values()).parallelStream().map(x -> {
            ParseInModule pim = RuleGrammarGenerator.getCombinedGrammar(gen.getRuleGrammar(x), isStrict, profileRules, files);
            pim.getScanner(options.global);
            return new Tuple2<>(x, pim);
        }).collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));

        // do parsing on remaining bubbles and collect everything in `parsedSentences`
        // this way we can easily parallelize the steps and we don't have to deal with the complex structure of modules
        Map<String, java.util.Set<Sentence>> parsedSentences = new HashMap<>();
        stream(defWithCaches.modules())
                .parallel()
                .map(m -> {
                    if (stream(m.localSentences()).noneMatch(s -> s instanceof Bubble))
                        return m;
                    ParseInModule pim = RuleGrammarGenerator.getCombinedGrammar(gen.getRuleGrammar(m), isStrict, profileRules, files);
                    pim.setScanner(donorScanners.get(donorModule.get(m.name())).getScanner());
                    pim.initialize();
                    ParseCache cache = loadCache(pim.seedModule());
                    java.util.Set<Sentence> sentences = stream(m.localSentences()).filter(s -> s instanceof Bubble)
                            .map(s -> (Bubble) s)
                            .parallel()
                            .flatMap(b -> {
                                Tuple2<Either<java.util.Set<KEMException>, K>, java.util.Set<KEMException>> result;
                                int startLine = b.att().get("contentStartLine", Integer.class);
                                int startColumn = b.att().get("contentStartColumn", Integer.class);
                                Source source = b.att().get(Source.class);
                                result = pim.parseString(b.contents(), START_SYMBOL, pim.getScanner(), source, startLine, startColumn, true, b.att().contains(Att.ANYWHERE()) || b.att().contains(Att.SIMPLIFICATION()) || ExpandMacros.isMacro(b));
                                parsedBubbles.getAndIncrement();
                                if (kem.options.warnings2errors && !result._2().isEmpty()) {
                                    for (KEMException err : result._2()) {
                                        if (kem.options.includesExceptionType(err.exception.getType())) {
                                            errors.add(KEMException.asError(err));
                                        }
                                    }
                                } else {
                                    kem.addAllKException(result._2().stream().map(e -> e.getKException()).collect(Collectors.toList()));
                                }
                                if (result._1().isRight()) {
                                    KApply k = (KApply) new TreeNodesToKORE(Outer::parseSort, isStrict).down(result._1().right().get());
                                    k = KApply(k.klabel(), k.klist(), k.att().addAll(b.att().remove("contentStartLine").remove("contentStartColumn").remove(Source.class).remove(Location.class)));
                                    cache.getCache().put(b.contents(), new ParsedSentence(k, new HashSet<>(result._2())));
                                    return Stream.of(upSentence(k, b.sentenceType()));
                                } else {
                                    errors.addAll(result._1().left().get());
                                    return Stream.empty();
                                }
                            }).collect(Collectors.toSet());
                    synchronized (parsedSentences) {
                        parsedSentences.put(m.name(), sentences);
                    }
                    return m;
                }).collect(Collectors.toSet());

        // replace bubbles with parsed sentences
        return DefinitionTransformer.from(m -> {
            if (parsedSentences.get(m.name()) == null || parsedSentences.get(m.name()).isEmpty())
                return m;
            java.util.Set<Sentence> noBubbles = stream(m.localSentences()).filter(s -> !(s instanceof Bubble)).collect(Collectors.toSet());
            noBubbles.addAll(parsedSentences.get(m.name())); // doing it with java because scala filter gives a NoSuchMethodError when using $plus$plus
            return Module(m.name(), m.imports(), immutable(noBubbles), m.att());
        }, "parsing rules").apply(defWithCaches);
    }

    public Rule parseRule(CompiledDefinition compiledDef, String contents, Source source) {
        errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
        gen = new RuleGrammarGenerator(compiledDef.kompiledDefinition);
        try (ParseInModule parser = RuleGrammarGenerator
                .getCombinedGrammar(gen.getRuleGrammar(compiledDef.executionModule()), isStrict, profileRules, files)) {
            java.util.Set<K> res = performParse(new HashMap<>(), parser, parser.getScanner(),
                    new Bubble(rule, contents, Att().add("contentStartLine", Integer.class, 1)
                            .add("contentStartColumn", Integer.class, 1).add(Source.class, source)))
                    .collect(Collectors.toSet());
            if (!errors.isEmpty()) {
                throw errors.iterator().next();
            }
            return upRule(res.iterator().next());
        }
    }

    private Sentence upSentence(K contens, String sentenceType) {
        switch (sentenceType) {
        case claim:         return upClaim(contens);
        case rule:          return upRule(contens);
        case context:       return upContext(contens);
        case alias:         return upAlias(contens);
        }
        throw new AssertionError("Unexpected sentence type: " + sentenceType);
    }

    private Claim upClaim(K contents) {
        KApply ruleContents = (KApply) contents;
        List<org.kframework.kore.K> items = ruleContents.klist().items();
        switch (ruleContents.klabel().name()) {
        case "#ruleNoConditions":
            return Claim(items.get(0), BooleanUtils.TRUE, BooleanUtils.TRUE, ruleContents.att());
        case "#ruleRequires":
            return Claim(items.get(0), items.get(1), BooleanUtils.TRUE, ruleContents.att());
        case "#ruleEnsures":
            return Claim(items.get(0), BooleanUtils.TRUE, items.get(1), ruleContents.att());
        case "#ruleRequiresEnsures":
            return Claim(items.get(0), items.get(1), items.get(2), ruleContents.att());
        default:
            throw new AssertionError("Wrong KLabel for claim content");
        }
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

    private ContextAlias upAlias(K contents) {
        KApply ruleContents = (KApply) contents;
        List<K> items = ruleContents.klist().items();
        switch (ruleContents.klabel().name()) {
        case "#ruleNoConditions":
            return ContextAlias(items.get(0), BooleanUtils.TRUE, ruleContents.att());
        case "#ruleRequires":
            return ContextAlias(items.get(0), items.get(1), ruleContents.att());
        default:
            throw KEMException.criticalError("Illegal context alias with ensures clause detected.", contents);
        }
    }

    private ParseCache loadCache(Module parser) {
        ParseCache cachedParser = caches.get(parser.name());
        if (cachedParser == null || !equalsSyntax(cachedParser.getModule(), parser) || cachedParser.isStrict() != isStrict) {
            cachedParser = new ParseCache(parser, isStrict, java.util.Collections.synchronizedMap(new HashMap<>()));
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

    private Stream<? extends K> performParse(Map<String, ParsedSentence> cache, ParseInModule parser, Scanner scanner, Bubble b) {
        int startLine = b.att().get("contentStartLine", Integer.class);
        int startColumn = b.att().get("contentStartColumn", Integer.class);
        Source source = b.att().get(Source.class);
        Tuple2<Either<java.util.Set<KEMException>, K>, java.util.Set<KEMException>> result;
        if (cache.containsKey(b.contents())) {
            ParsedSentence parse = cache.get(b.contents());
            cachedBubbles.getAndIncrement();
            if (kem.options.warnings2errors) {
                for (KEMException err : parse.getWarnings().stream().map(e -> (KEMException) e).collect(Collectors.toList())) {
                    if (kem.options.includesExceptionType(err.exception.getType())) {
                        errors.add(KEMException.asError(err));
                    }
                }
            } else {
                kem.addAllKException(parse.getWarnings().stream().map(e -> e.getKException()).collect(Collectors.toList()));
            }
            Att att = parse.getParse().att().addAll(b.att().remove("contentStartLine").remove("contentStartColumn").remove(Source.class).remove(Location.class));
            return Stream.of(new AddAtt(a -> att).apply(parse.getParse()));
        }
        result = parser.parseString(b.contents(), START_SYMBOL, scanner, source, startLine, startColumn, true, b.att().contains(Att.ANYWHERE()) || b.att().contains(Att.SIMPLIFICATION()) || ExpandMacros.isMacro(b));
        parsedBubbles.getAndIncrement();
        if (kem.options.warnings2errors && !result._2().isEmpty()) {
          for (KEMException err : result._2()) {
            if (kem.options.includesExceptionType(err.exception.getType())) {
              errors.add(KEMException.asError(err));
            }
          }
        } else {
          kem.addAllKException(result._2().stream().map(e -> e.getKException()).collect(Collectors.toList()));
        }
        if (result._1().isRight()) {
            KApply k = (KApply) new TreeNodesToKORE(Outer::parseSort, isStrict).down(result._1().right().get());
            k = KApply(k.klabel(), k.klist(), k.att().addAll(b.att().remove("contentStartLine").remove("contentStartColumn").remove(Source.class).remove(Location.class)));
            cache.put(b.contents(), new ParsedSentence(k, new HashSet<>(result._2())));
            return Stream.of(k);
        } else {
            errors.addAll(result._1().left().get());
            return Stream.empty();
        }
    }
}
