// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kompile;

import static org.kframework.Collections.*;
import static org.kframework.builtin.KLabels.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.definition.Constructors.Module;
import static org.kframework.kore.KORE.*;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.collections4.ListUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.GenerateSentencesFromConfigDecl;
import org.kframework.compile.checks.CheckRegex;
import org.kframework.definition.Bubble;
import org.kframework.definition.Claim;
import org.kframework.definition.Configuration;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxSort;
import org.kframework.kore.AddAttRec;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KToken;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ParserUtils;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.inner.ParseCache;
import org.kframework.parser.inner.ParseCache.ParsedSentence;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.parser.inner.kernel.Scanner;
import org.kframework.parser.json.JsonParser;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import scala.Option;
import scala.Tuple2;
import scala.collection.Set;
import scala.util.Either;

/**
 * A bundle of code doing various aspects of definition parsing. TODO: In major need of refactoring.
 *
 * @cos refactored this code out of Kompile but none (or close to none) of it was originally written
 *     by him.
 */
public class DefinitionParsing {
  public static final Sort START_SYMBOL = Sorts.RuleContent();
  public static final String rule = "rule";
  public static final String claim = "claim";
  public static final String configuration = "config";
  public static final String alias = "alias";
  public static final String context = "context";
  private final File cacheFile;
  private final boolean autoImportDomains;
  private final KompileOptions options;
  private final GlobalOptions globalOptions;
  private final OuterParsingOptions outerParsingOptions;

  private final KExceptionManager kem;
  private final FileUtil files;
  private final ParserUtils parser;
  private final boolean cacheParses;
  private final BinaryLoader loader;
  private final Stopwatch sw;

  public final AtomicInteger parsedBubbles = new AtomicInteger(0);
  public final AtomicInteger cachedBubbles = new AtomicInteger(0);
  private final boolean profileRules;
  private final List<File> lookupDirectories;
  private final InnerParsingOptions innerParsingOptions;

  public DefinitionParsing(
      List<File> lookupDirectories,
      KompileOptions options,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      KExceptionManager kem,
      FileUtil files,
      ParserUtils parser,
      boolean cacheParses,
      File cacheFile,
      Stopwatch sw) {
    this.lookupDirectories = lookupDirectories;
    this.options = options;
    this.globalOptions = globalOptions;
    this.outerParsingOptions = outerParsingOptions;
    this.innerParsingOptions = innerParsingOptions;
    this.kem = kem;
    this.files = files;
    this.parser = parser;
    this.cacheParses = cacheParses;
    this.cacheFile = cacheFile;
    this.autoImportDomains = !outerParsingOptions.noPrelude;
    this.loader = new BinaryLoader(this.kem);
    this.profileRules = innerParsingOptions.profileRules != null;
    this.sw = sw;
  }

  public java.util.Set<Module> parseModules(
      CompiledDefinition definition,
      KompileOptions.MainModule mainModule,
      String entryPointModule,
      File definitionFile,
      java.util.Set<Att.Key> excludeModules,
      boolean readOnlyCache,
      boolean useCachedScanner) {
    Definition def =
        parser.loadDefinition(
            mainModule,
            mutable(definition.getParsedDefinition().modules()),
            FileUtil.load(definitionFile),
            Source.apply(definitionFile.getAbsolutePath()),
            definitionFile.getParentFile(),
            ListUtils.union(Lists.newArrayList(Kompile.BUILTIN_DIRECTORY), lookupDirectories),
            options.preprocess,
            options.bisonLists);

    if (!def.getModule(mainModule.name()).isDefined()) {
      throw KEMException.criticalError("Module " + mainModule + " does not exist.");
    }
    if (!def.getModule(entryPointModule).isDefined()) {
      throw KEMException.criticalError("Module " + entryPointModule + " does not exist.");
    }
    if (profileRules) {
      // create the temp dir ahead of parsing to avoid a race condition
      files.resolveTemp(".");
    }
    Stream<Module> modules = Stream.of(def.getModule(mainModule.name()).get());
    modules =
        Stream.concat(modules, stream(def.getModule(mainModule.name()).get().importedModules()));
    modules = Stream.concat(modules, Stream.of(def.getModule(entryPointModule).get()));
    modules =
        Stream.concat(modules, stream(def.getModule(entryPointModule).get().importedModules()));
    modules =
        Stream.concat(
            modules,
            stream(def.entryModules())
                .filter(m -> stream(m.sentences()).noneMatch(s -> s instanceof Bubble)));
    def = Definition(def.mainModule(), immutable(modules.collect(Collectors.toSet())), def.att());

    def = Kompile.excludeModulesByTag(excludeModules, entryPointModule).apply(def);

    errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
    caches = loadCaches();

    stream(def.modules()).forEach(m -> CheckRegex.check(errors, m));
    throwExceptionIfThereAreErrors();
    sw.printIntermediate("Outer parsing [" + def.modules().size() + " modules]");

    try {
      def = resolveConfigBubbles(def);
    } catch (KEMException e) {
      errors.add(e);
      throwExceptionIfThereAreErrors();
      throw new AssertionError("should not reach this statement");
    }

    def = resolveNonConfigBubbles(def, false, useCachedScanner);
    saveTimings();
    if (!readOnlyCache) {
      saveCaches();
    }
    throwExceptionIfThereAreErrors();
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

  public Definition parseDefinitionAndResolveBubbles(
      File definitionFile,
      KompileOptions.MainModule mainModuleName,
      KompileOptions.SyntaxModule mainProgramsModule,
      java.util.Set<Att.Key> excludedModuleTags) {
    Definition parsedDefinition =
        parseDefinition(definitionFile, mainModuleName, mainProgramsModule);
    Stream<Module> modules = Stream.of(parsedDefinition.mainModule());
    modules = Stream.concat(modules, stream(parsedDefinition.mainModule().importedModules()));
    Option<Module> syntaxModule = parsedDefinition.getModule(mainProgramsModule.name());
    if (syntaxModule.isDefined()) {
      modules = Stream.concat(modules, Stream.of(syntaxModule.get()));
      modules = Stream.concat(modules, stream(syntaxModule.get().importedModules()));
    }
    modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("K-REFLECTION").get()));
    modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("STDIN-STREAM").get()));
    modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("STDOUT-STREAM").get()));
    modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("MAP").get()));
    if (options.coverage) {
      modules = Stream.concat(modules, Stream.of(parsedDefinition.getModule("K-IO").get()));
      modules =
          Stream.concat(
              modules, stream(parsedDefinition.getModule("K-IO").get().importedModules()));
    }
    modules =
        Stream.concat(
            modules,
            stream(parsedDefinition.entryModules())
                .filter(m -> stream(m.sentences()).noneMatch(s -> s instanceof Bubble)));
    Definition trimmed =
        Definition(
            parsedDefinition.mainModule(),
            immutable(modules.collect(Collectors.toSet())),
            parsedDefinition.att());
    trimmed =
        Kompile.excludeModulesByTag(excludedModuleTags, mainProgramsModule.name()).apply(trimmed);

    errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
    stream(trimmed.modules()).forEach(m -> CheckRegex.check(errors, m));
    throwExceptionIfThereAreErrors();

    sw.printIntermediate("Outer parsing [" + trimmed.modules().size() + " modules]");
    if (profileRules) {
      // create the temp dir ahead of parsing to avoid a race condition
      files.resolveTemp(".");
    }
    Definition afterResolvingConfigBubbles =
        resolveConfigBubbles(trimmed, parsedDefinition.getModule("DEFAULT-CONFIGURATION").get());
    sw.printIntermediate(
        "Parse configurations ["
            + parsedBubbles.get()
            + "/"
            + (parsedBubbles.get() + cachedBubbles.get())
            + " declarations]");
    parsedBubbles.set(0);
    cachedBubbles.set(0);
    Definition afterResolvingAllOtherBubbles =
        resolveNonConfigBubbles(afterResolvingConfigBubbles, true, false);
    sw.printIntermediate(
        "Parse rules ["
            + parsedBubbles.get()
            + "/"
            + (parsedBubbles.get() + cachedBubbles.get())
            + " rules]");
    saveTimings();
    saveCachesAndReportParsingErrors();
    return afterResolvingAllOtherBubbles;
  }

  private void throwExceptionIfThereAreErrors() {
    if (!errors.isEmpty()) {
      kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
      throw KEMException.compilerError("Had " + errors.size() + " parsing errors.");
    }
  }

  public Definition parseDefinition(
      File definitionFile,
      KompileOptions.MainModule mainModuleName,
      KompileOptions.SyntaxModule mainProgramsModule) {
    if (options.outerParsedJson) {
      return JsonParser.parseDefinition(FileUtil.load(definitionFile));
    } else {
      return parser.loadDefinition(
          mainModuleName,
          mainProgramsModule,
          FileUtil.load(definitionFile),
          definitionFile,
          definitionFile.getParentFile(),
          ListUtils.union(lookupDirectories, Lists.newArrayList(Kompile.BUILTIN_DIRECTORY)),
          autoImportDomains,
          options.preprocess,
          options.bisonLists);
    }
  }

  protected Definition resolveConfigBubbles(Definition definition, Module defaultConfiguration) {
    Definition definitionWithConfigBubble =
        DefinitionTransformer.from(
                mod -> {
                  if (mod.name().equals(definition.mainModule().name())) {
                    boolean hasConfigDecl =
                        stream(mod.sentences())
                            .anyMatch(
                                s ->
                                    s instanceof Bubble
                                        && ((Bubble) s).sentenceType().equals(configuration));
                    if (!hasConfigDecl) {
                      return Module(
                          mod.name(),
                          mod.imports().$bar(Set(Import(defaultConfiguration, true))).toSet(),
                          mod.localSentences(),
                          mod.att());
                    }
                  }
                  return mod;
                },
                "adding default configuration")
            .apply(definition);

    Module mapModule =
        definitionWithConfigBubble
            .getModule("MAP")
            .getOrElse(
                () -> {
                  throw KEMException.compilerError(
                      "Module MAP must be visible at the configuration declaration");
                });
    Definition definitionWithMapForConfig =
        DefinitionTransformer.from(
                mod -> {
                  long numConfigDecl =
                      stream(mod.localSentences())
                          .filter(
                              s ->
                                  s instanceof Bubble
                                      && ((Bubble) s).sentenceType().equals(configuration))
                          .count();
                  if (numConfigDecl == 1) {
                    return Module(
                        mod.name(),
                        mod.imports().$bar(Set(Import(mapModule, true))).toSet(),
                        mod.localSentences(),
                        mod.att());
                  } else if (numConfigDecl != 0) {
                    throw KEMException.compilerError(
                        "Only one configuration declaration may be declared per module. Found "
                            + numConfigDecl
                            + " in module "
                            + mod.name()
                            + ".");
                  }
                  return mod;
                },
                "adding MAP to modules with configs")
            .apply(definitionWithConfigBubble);

    errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
    caches = loadCaches();

    Definition result;
    try {
      result = resolveConfigBubbles(definitionWithMapForConfig);
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

  public java.util.Set<KEMException> errors() {
    return errors;
  }

  private void checkConfigCells(Definition defWithParsedConfigs) {
    // check for duplicate <k> cell declarations
    List<K> kcells = new ArrayList<>();
    stream(defWithParsedConfigs.mainModule().sentences())
        .filter(s -> s instanceof Configuration)
        .forEach(
            s ->
                new VisitK() {
                  @Override
                  public void apply(KApply k) {
                    if (k.klabel().equals(KLabel("#configCell"))) {
                      KToken kt = (KToken) k.klist().items().get(0);
                      assert kt.sort().equals(Sorts.CellName());
                      if (kt.s().equals("k")) kcells.add(k);
                      else if (kt.s().equals(GENERATED_TOP_CELL_NAME)
                          || kt.s().equals(GENERATED_COUNTER_CELL_NAME)) {
                        // check for definitions of generated cell names
                        errors.add(
                            KEMException.compilerError(
                                "Cell name <" + kt.s() + "> is reserved by K.", kt));
                      }
                    }
                    super.apply(k);
                  }
                }.apply(((Configuration) s).body()));
    if (kcells.size() <= 1) {
      return;
    }
    for (K kCellDecl : kcells) {
      this.errors.add(
          KEMException.compilerError(
              "Multiple K cell declarations detected. Only one <k> cell declaration is allowed.",
              kCellDecl));
    }
    throwExceptionIfThereAreErrors();
  }

  private Definition resolveConfigBubbles(Definition def) {
    Definition defWithCaches = resolveCachedBubbles(def, false);
    RuleGrammarGenerator gen = new RuleGrammarGenerator(def);

    // parse config bubbles in parallel
    // step 1 - use scala parallel streams to generate parsers
    // step 2 - use java parallel streams to parse sentences
    // this avoids creation of extra (costly) threads at the cost
    // of a small thread contention between the two thread pools
    Map<String, Module> parsed =
        defWithCaches.parMap(
            m -> {
              if (stream(m.localSentences())
                  .noneMatch(
                      s ->
                          s instanceof Bubble && ((Bubble) s).sentenceType().equals(configuration)))
                return m;
              Module configParserModule = gen.getConfigGrammar(m);
              ParseCache cache = loadCache(configParserModule);
              try (ParseInModule parser =
                  RuleGrammarGenerator.getCombinedGrammar(
                      cache.module(),
                      profileRules,
                      files,
                      options.debugTypeInference,
                      innerParsingOptions.typeInferenceMode)) {
                // each parser gets its own scanner because config labels can conflict with user
                // tokens
                parser.getScanner(globalOptions);
                parser.initialize();

                java.util.Set<Sentence> parsedSet =
                    stream(m.localSentences())
                        .filter(
                            s ->
                                s instanceof Bubble
                                    && ((Bubble) s).sentenceType().equals(configuration))
                        .map(b -> (Bubble) b)
                        .parallel()
                        .flatMap(
                            b ->
                                parseBubble(parser, cache.cache(), b)
                                    .map(p -> upSentence(p, b.sentenceType())))
                        .collect(Collectors.toSet());
                scala.collection.immutable.Set<Sentence> allSent =
                    m.localSentences()
                        .$bar(immutable(parsedSet))
                        .filter(
                            s ->
                                !(s instanceof Bubble
                                    && ((Bubble) s).sentenceType().equals(configuration)))
                        .toSet();
                return Module(m.name(), m.imports(), allSent, m.att());
              }
            });

    Definition defWithParsedConfigs =
        DefinitionTransformer.from(
                m -> Module(m.name(), m.imports(), parsed.get(m.name()).localSentences(), m.att()),
                "replace configs")
            .apply(defWithCaches);

    checkConfigCells(defWithParsedConfigs);

    // replace config bubbles with the generated syntax and rules
    return DefinitionTransformer.from(
            m -> {
              if (stream(m.localSentences())
                  .noneMatch(
                      s ->
                          s instanceof Configuration
                              || (s instanceof SyntaxSort
                                  && s.att().contains(Att.TEMPORARY_CELL_SORT_DECL())))) return m;

              Set<Sentence> importedConfigurationSortsSubsortedToCell =
                  stream(m.productions())
                      .filter(p -> p.att().contains(Att.CELL()))
                      .map(p -> Production(Seq(), Sorts.Cell(), Seq(NonTerminal(p.sort()))))
                      .collect(toSet());

              Module module =
                  Module(
                      m.name(),
                      m.imports(),
                      m.localSentences().$bar(importedConfigurationSortsSubsortedToCell).toSet(),
                      m.att());

              Module extMod =
                  RuleGrammarGenerator.getCombinedGrammar(
                          gen.getConfigGrammar(module),
                          profileRules,
                          files,
                          options.debugTypeInference,
                          innerParsingOptions.typeInferenceMode)
                      .getExtensionModule();
              Set<Sentence> configDeclProductions =
                  stream(module.localSentences())
                      .filter(s -> s instanceof Configuration)
                      .map(b -> (Configuration) b)
                      .flatMap(
                          configDecl ->
                              stream(
                                  GenerateSentencesFromConfigDecl.gen(
                                      kem,
                                      configDecl.body(),
                                      configDecl.ensures(),
                                      configDecl.att(),
                                      extMod)))
                      .collect(toSet());

              scala.collection.immutable.Set<Sentence> stc =
                  immutable(
                      stream(m.localSentences().union(configDeclProductions))
                          .filter(s -> !(s instanceof Configuration))
                          .filter(
                              s ->
                                  !(s instanceof SyntaxSort ss
                                      && ss.att().contains(Att.TEMPORARY_CELL_SORT_DECL())))
                          .collect(Collectors.toSet()));
              Module newM = Module(m.name(), m.imports(), stc, m.att());
              newM.checkSorts(); // ensure all the Cell sorts are defined
              return newM;
            },
            "expand configs")
        .apply(defWithParsedConfigs);
  }

  private Definition resolveNonConfigBubbles(
      Definition defWithConfig, boolean serializeScanner, boolean deserializeScanner) {
    Definition defWithCaches = resolveCachedBubbles(defWithConfig, true);
    RuleGrammarGenerator gen = new RuleGrammarGenerator(defWithCaches);
    Module ruleParserModule = gen.getRuleGrammar(defWithCaches.mainModule());
    ParseCache cache = loadCache(ruleParserModule);
    try (ParseInModule parser =
        RuleGrammarGenerator.getCombinedGrammar(
            cache.module(),
            profileRules,
            false,
            true,
            files,
            options.debugTypeInference,
            innerParsingOptions.typeInferenceMode,
            false)) {
      Scanner scanner;
      if (deserializeScanner) {
        scanner = new Scanner(parser, globalOptions, files.resolveKompiled("scanner"));
        parser.setScanner(scanner);
      } else {
        scanner = parser.getScanner(globalOptions);
        if (serializeScanner) {
          scanner.serialize(files.resolveKompiled("scanner"));
        }
      }
      final Scanner realScanner = scanner;
      Map<String, Module> parsed =
          defWithCaches.parMap(m -> this.resolveNonConfigBubbles(m, realScanner, gen));
      return DefinitionTransformer.from(
              m -> Module(m.name(), m.imports(), parsed.get(m.name()).localSentences(), m.att()),
              "parsing rules")
          .apply(defWithConfig);
    }
  }

  private Module resolveNonConfigBubbles(Module module, Scanner scanner, RuleGrammarGenerator gen) {
    if (stream(module.localSentences()).noneMatch(s -> s instanceof Bubble)) return module;

    Module ruleParserModule = gen.getRuleGrammar(module);
    // this scanner is not good for this module, so we must generate a new scanner.
    boolean needNewScanner = !scanner.getModule().importedModuleNames().contains(module.name());

    ParseCache cache = loadCache(ruleParserModule);
    try (ParseInModule parser =
        needNewScanner
            ? RuleGrammarGenerator.getCombinedGrammar(
                cache.module(),
                profileRules,
                files,
                options.debugTypeInference,
                innerParsingOptions.typeInferenceMode)
            : RuleGrammarGenerator.getCombinedGrammar(
                cache.module(),
                scanner,
                profileRules,
                false,
                files,
                options.debugTypeInference,
                innerParsingOptions.typeInferenceMode,
                false)) {
      if (needNewScanner) parser.getScanner(globalOptions);
      parser.initialize();

      Set<Sentence> parsedSet =
          stream(module.localSentences())
              .parallel()
              .filter(s -> s instanceof Bubble)
              .map(b -> (Bubble) b)
              .flatMap(
                  b ->
                      parseBubble(parser, cache.cache(), b)
                          .map(p -> upSentence(p, b.sentenceType())))
              .collect(Collections.toSet());

      if (needNewScanner) {
        parser.getScanner().close(); // required for Windows.
      }

      return Module(
          module.name(),
          module.imports(),
          Collections.immutable(
              stream(module.localSentences().$bar(parsedSet))
                  .filter(b -> !(b instanceof Bubble))
                  .collect(Collectors.toSet())),
          module.att());
    }
  }

  /**
   * Replace all the targeted Bubbles from the definition if they can be found in caches.
   *
   * @param def The Definition with Bubbles.
   * @param isRule true if it should target non config Bubbles, false if it should parse only config
   *     bubbles
   * @return A new Definition object with Bubbles replaced by the appropriate Sentence type.
   */
  private Definition resolveCachedBubbles(Definition def, boolean isRule) {
    RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
    return DefinitionTransformer.from(
            m -> {
              if (stream(m.localSentences())
                  .noneMatch(
                      s ->
                          s instanceof Bubble
                              && (isRule || ((Bubble) s).sentenceType().equals(configuration))))
                return m;
              ParseCache cache =
                  isRule ? loadCache(gen.getRuleGrammar(m)) : loadCache(gen.getConfigGrammar(m));

              Map<Bubble, Sentence> fromCache =
                  stream(m.localSentences())
                      .filter(
                          s ->
                              s instanceof Bubble
                                  && (isRule || ((Bubble) s).sentenceType().equals(configuration)))
                      .map(b -> (Bubble) b)
                      .flatMap(
                          b -> {
                            if (cache.cache().containsKey(b.contents())
                                && cache.cache().get(b.contents()).parse() != null) {
                              ParsedSentence parse =
                                  updateLocation(cache.cache().get(b.contents()), b);
                              Att termAtt =
                                  parse
                                      .parse()
                                      .att()
                                      .remove(Att.SOURCE(), Source.class)
                                      .remove(Att.LOCATION(), Location.class)
                                      .remove(Att.PRODUCTION(), Production.class);
                              Att bubbleAtt =
                                  b.att()
                                      .remove(Att.SOURCE(), Source.class)
                                      .remove(Att.LOCATION(), Location.class)
                                      .remove(Att.CONTENT_START_LINE(), Integer.class)
                                      .remove(Att.CONTENT_START_COLUMN(), Integer.class);
                              if (!termAtt.equals(bubbleAtt)) {
                                // invalidate cache if attributes changed
                                return Stream.of();
                              }
                              cachedBubbles.getAndIncrement();
                              registerWarnings(parse.warnings());
                              KApply k =
                                  (KApply)
                                      new TreeNodesToKORE(Outer::parseSort).down(parse.parse());
                              return Stream.of(Pair.of(b, upSentence(k, b.sentenceType())));
                            }
                            return Stream.of();
                          })
                      .collect(Collectors.toMap(Pair::getKey, Pair::getValue));

              if (!fromCache.isEmpty()) {
                scala.collection.immutable.Set<Sentence> stc =
                    m.localSentences()
                        .$bar(immutable(Sets.newHashSet(fromCache.values())))
                        .filter(s -> !(s instanceof Bubble && fromCache.containsKey(s)))
                        .toSet();
                return Module(m.name(), m.imports(), stc, m.att());
              }
              return m;
            },
            "load cached bubbles")
        .apply(def);
  }

  public static ParsedSentence updateLocation(ParsedSentence parse, Bubble b) {
    int newStartLine = b.att().get(Att.CONTENT_START_LINE(), Integer.class);
    int newStartColumn = b.att().get(Att.CONTENT_START_COLUMN(), Integer.class);
    int oldStartLine = parse.startLine();
    int oldStartColumn = parse.startColumn();
    if (oldStartLine != newStartLine
        || oldStartColumn != newStartColumn
        || !parse.source().equals(b.source().get())) {
      int lineOffset = newStartLine - oldStartLine;
      int columnOffset = newStartColumn - oldStartColumn;
      K k =
          parse.parse() != null
              ? new AddAttRec(
                      a -> {
                        Location loc = a.get(Att.LOCATION(), Location.class);
                        Location newLoc =
                            updateLocation(oldStartLine, lineOffset, columnOffset, loc);
                        return a.remove(Att.SOURCE(), Source.class)
                            .remove(Att.LOCATION(), Location.class)
                            .add(Att.LOCATION(), Location.class, newLoc)
                            .add(
                                Att.SOURCE(),
                                Source.class,
                                b.source()
                                    .orElseThrow(
                                        () ->
                                            new AssertionError(
                                                "Expecting bubble to have source location!")));
                      })
                  .apply(parse.parse())
              : null;
      java.util.Set<KEMException> warnings =
          parse.warnings().stream()
              .map(
                  ex ->
                      ex.withLocation(
                          updateLocation(
                              oldStartLine, lineOffset, columnOffset, ex.exception.getLocation()),
                          b.source()
                              .orElseThrow(
                                  () ->
                                      new AssertionError(
                                          "Expecting bubble to have source location!"))))
              .collect(Collectors.toSet());
      java.util.Set<KEMException> errors =
          parse.errors().stream()
              .map(
                  ex ->
                      ex.withLocation(
                          updateLocation(
                              oldStartLine, lineOffset, columnOffset, ex.exception.getLocation()),
                          b.source()
                              .orElseThrow(
                                  () ->
                                      new AssertionError(
                                          "Expecting bubble to have source location!"))))
              .collect(Collectors.toSet());
      return new ParsedSentence(k, warnings, errors, newStartLine, newStartColumn, parse.source());
    }
    return parse;
  }

  private static Location updateLocation(
      int oldStartLine, int lineOffset, int columnOffset, Location loc) {
    return Location.apply(
        loc.startLine() + lineOffset,
        // only the first line can have column offset, otherwise it will trigger a cache miss
        oldStartLine == loc.startLine() ? loc.startColumn() + columnOffset : loc.startColumn(),
        loc.endLine() + lineOffset,
        oldStartLine == loc.endLine() ? loc.endColumn() + columnOffset : loc.endColumn());
  }

  private void registerWarnings(java.util.Set<KEMException> warnings) {
    if (kem.options.warnings2errors) {
      for (KEMException err : warnings) {
        if (kem.options.includesExceptionType(err.exception.getType())) {
          errors.add(KEMException.asError(err));
        }
      }
    } else {
      kem.addAllKException(
          warnings.stream().map(KEMException::getKException).collect(Collectors.toList()));
    }
  }

  public Rule parseRule(CompiledDefinition compiledDef, String contents, Source source) {
    errors = java.util.Collections.synchronizedSet(Sets.newHashSet());
    RuleGrammarGenerator gen = new RuleGrammarGenerator(compiledDef.kompiledDefinition);
    try (ParseInModule parser =
        RuleGrammarGenerator.getCombinedGrammar(
            gen.getRuleGrammar(compiledDef.getParsedDefinition().mainModule()),
            profileRules,
            false,
            true,
            files,
            options.debugTypeInference,
            innerParsingOptions.typeInferenceMode,
            false)) {
      parser.setScanner(new Scanner(parser, globalOptions, files.resolveKompiled("scanner")));
      java.util.Set<K> res =
          parseBubble(
                  parser,
                  new HashMap<>(),
                  new Bubble(
                      rule,
                      contents,
                      Att.empty()
                          .add(Att.CONTENT_START_LINE(), 1)
                          .add(Att.CONTENT_START_COLUMN(), 1)
                          .add(Att.SOURCE(), Source.class, source)))
              .collect(Collectors.toSet());
      if (!errors.isEmpty()) {
        throw errors.iterator().next();
      }
      return upRule(res.iterator().next());
    }
  }

  private Sentence upSentence(K contents, String sentenceType) {
    switch (sentenceType) {
      case claim:
        return upClaim(contents);
      case rule:
        return upRule(contents);
      case context:
        return upContext(contents);
      case alias:
        return upAlias(contents);
      case configuration:
        return upConfiguration(contents);
    }
    throw new AssertionError("Unexpected sentence type: " + sentenceType);
  }

  private Claim upClaim(K contents) {
    KApply ruleContents = (KApply) contents;
    List<org.kframework.kore.K> items = ruleContents.klist().items();
    return switch (ruleContents.klabel().name()) {
      case "#ruleNoConditions" -> Claim(
          items.get(0), BooleanUtils.TRUE, BooleanUtils.TRUE, ruleContents.att());
      case "#ruleRequires" -> Claim(
          items.get(0), items.get(1), BooleanUtils.TRUE, ruleContents.att());
      case "#ruleEnsures" -> Claim(
          items.get(0), BooleanUtils.TRUE, items.get(1), ruleContents.att());
      case "#ruleRequiresEnsures" -> Claim(
          items.get(0), items.get(1), items.get(2), ruleContents.att());
      default -> throw new AssertionError("Wrong KLabel for claim content");
    };
  }

  private Rule upRule(K contents) {
    KApply ruleContents = (KApply) contents;
    List<org.kframework.kore.K> items = ruleContents.klist().items();
    return switch (ruleContents.klabel().name()) {
      case "#ruleNoConditions" -> Rule(
          items.get(0), BooleanUtils.TRUE, BooleanUtils.TRUE, ruleContents.att());
      case "#ruleRequires" -> Rule(
          items.get(0), items.get(1), BooleanUtils.TRUE, ruleContents.att());
      case "#ruleEnsures" -> Rule(
          items.get(0), BooleanUtils.TRUE, items.get(1), ruleContents.att());
      case "#ruleRequiresEnsures" -> Rule(
          items.get(0), items.get(1), items.get(2), ruleContents.att());
      default -> throw new AssertionError("Wrong KLabel for rule content");
    };
  }

  private Context upContext(K contents) {
    KApply ruleContents = (KApply) contents;
    List<K> items = ruleContents.klist().items();
    return switch (ruleContents.klabel().name()) {
      case "#ruleNoConditions" -> Context(items.get(0), BooleanUtils.TRUE, ruleContents.att());
      case "#ruleRequires" -> Context(items.get(0), items.get(1), ruleContents.att());
      default -> throw KEMException.criticalError(
          "Illegal context with ensures clause detected.", contents);
    };
  }

  private ContextAlias upAlias(K contents) {
    KApply ruleContents = (KApply) contents;
    List<K> items = ruleContents.klist().items();
    return switch (ruleContents.klabel().name()) {
      case "#ruleNoConditions" -> ContextAlias(items.get(0), BooleanUtils.TRUE, ruleContents.att());
      case "#ruleRequires" -> ContextAlias(items.get(0), items.get(1), ruleContents.att());
      default -> throw KEMException.criticalError(
          "Illegal context alias with ensures clause detected.", contents);
    };
  }

  private Configuration upConfiguration(K contents) {
    KApply configContents = (KApply) contents;
    List<K> items = configContents.klist().items();
    return switch (configContents.klabel().name()) {
      case "#ruleNoConditions" -> Configuration(
          items.get(0), BooleanUtils.TRUE, configContents.att());
      case "#ruleEnsures" -> Configuration(items.get(0), items.get(1), configContents.att());
      default -> throw KEMException.compilerError(
          "Illegal configuration with requires clause detected.", configContents);
    };
  }

  private ParseCache loadCache(Module parser) {
    ParseCache cachedParser = caches.get(parser.name());
    if (cachedParser == null
        || !equalsSyntax(cachedParser.module().signature(), parser.signature())) {
      cachedParser =
          new ParseCache(parser, true, java.util.Collections.synchronizedMap(new HashMap<>()));
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

  private Stream<? extends K> parseBubble(
      ParseInModule pim, Map<String, ParsedSentence> cache, Bubble b) {
    int startLine = b.att().get(Att.CONTENT_START_LINE(), Integer.class);
    int startColumn = b.att().get(Att.CONTENT_START_COLUMN(), Integer.class);
    Source source = b.att().get(Att.SOURCE(), Source.class);
    boolean isAnywhere =
        b.att().contains(Att.ANYWHERE())
            || b.att().contains(Att.SIMPLIFICATION())
            || ExpandMacros.isMacro(b);
    Tuple2<Either<java.util.Set<KEMException>, K>, java.util.Set<KEMException>> result =
        pim.parseString(
            b.contents(),
            START_SYMBOL,
            "bubble parsing",
            pim.getScanner(),
            source,
            startLine,
            startColumn,
            isAnywhere);
    parsedBubbles.getAndIncrement();
    registerWarnings(result._2());
    if (result._1().isRight()) {
      KApply k = (KApply) result._1().right().get();
      k =
          KApply(
              k.klabel(),
              k.klist(),
              k.att()
                  .addAll(
                      b.att()
                          .remove(Att.CONTENT_START_LINE(), Integer.class)
                          .remove(Att.CONTENT_START_COLUMN(), Integer.class)
                          .remove(Att.SOURCE(), Source.class)
                          .remove(Att.LOCATION(), Location.class)));
      cache.put(
          b.contents(),
          new ParsedSentence(
              k, new HashSet<>(result._2()), new HashSet<>(), startLine, startColumn, source));
      k = (KApply) new TreeNodesToKORE(Outer::parseSort).down(k);
      return Stream.of(k);
    } else {
      cache.put(
          b.contents(),
          new ParsedSentence(
              null,
              new HashSet<>(result._2()),
              result._1().left().get(),
              startLine,
              startColumn,
              source));
      errors.addAll(result._1().left().get());
      return Stream.empty();
    }
  }

  // Save all the timing information collected during parsing in a single file specified at command
  // line.
  // Timing information is expected to have two parts:
  // 1. the comparable part - path:lineNumber
  // 2. the printable part which contains the timing information
  // The comparable part is used to sort each entry to provide a stable output.
  private void saveTimings() {
    if (innerParsingOptions.profileRules != null) {
      try {
        List<Tuple2<String, String>> msgs = new ArrayList<>();
        for (File f : files.resolveTemp(".").listFiles()) {
          if (f.getName().matches("timing.+\\.log")) {
            BufferedReader br = new BufferedReader(new FileReader(f));
            String path = br.readLine();
            String msg = br.readLine();
            msgs.add(Tuple2.apply(path, msg));
          }
        }
        msgs.sort(Comparator.comparing(Tuple2::_1));
        FileUtil.save(
            new File(innerParsingOptions.profileRules),
            msgs.stream().map(Tuple2::_2).collect(Collectors.joining("\n")));
      } catch (IOException e) {
        throw KEMException.internalError("Failed to open timing.log", e);
      }
    }
  }
}
