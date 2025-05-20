// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kompile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

import com.google.common.collect.Comparators;
import com.google.inject.Inject;
import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.io.FileUtils;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.Backends;
import org.kframework.builtin.Sorts;
import org.kframework.compile.*;
import org.kframework.compile.checks.CheckAnonymous;
import org.kframework.compile.checks.CheckAssoc;
import org.kframework.compile.checks.CheckAtt;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckDeprecated;
import org.kframework.compile.checks.CheckFunctions;
import org.kframework.compile.checks.CheckHOLE;
import org.kframework.compile.checks.CheckK;
import org.kframework.compile.checks.CheckKLabels;
import org.kframework.compile.checks.CheckLabels;
import org.kframework.compile.checks.CheckRHSVariables;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxGroups;
import org.kframework.compile.checks.CheckTokens;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.InputModes;
import org.kframework.parser.KRead;
import org.kframework.parser.ParserUtils;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.parser.json.JsonParser;
import org.kframework.unparser.ToJson;
import org.kframework.utils.OS;
import org.kframework.utils.RunProcess;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import scala.Function1;
import scala.Option;
import scala.collection.JavaConverters;

/**
 * The new compilation pipeline. Everything is just wired together and will need clean-up once we
 * deside on design. Tracked by #1442.
 */
public class Kompile {
  public static final File BUILTIN_DIRECTORY = JarInfo.getKIncludeDir().resolve("builtin").toFile();
  public static final String REQUIRE_PRELUDE_K = "requires \"prelude.md\"\n";

  public static final String CACHE_FILE_NAME = "cache.bin";

  private final KompileOptions kompileOptions;
  private final GlobalOptions globalOptions;
  private final FileUtil files;
  private final KExceptionManager kem;
  private final ParserUtils parser;
  private final Stopwatch sw;
  private final DefinitionParsing definitionParsing;
  private final OuterParsingOptions outerParsingOptions;
  private final InnerParsingOptions innerParsingOptions;
  java.util.Set<KEMException> errors;

  public Kompile(
      KompileOptions kompileOptions,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      FileUtil files,
      KExceptionManager kem,
      boolean cacheParses) {
    this(
        kompileOptions,
        outerParsingOptions,
        innerParsingOptions,
        globalOptions,
        files,
        kem,
        new Stopwatch(globalOptions),
        cacheParses);
  }

  public Kompile(
      KompileOptions kompileOptions,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      FileUtil files,
      KExceptionManager kem) {
    this(kompileOptions, outerParsingOptions, innerParsingOptions, globalOptions, files, kem, true);
  }

  @Inject
  public Kompile(
      KompileOptions kompileOptions,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      FileUtil files,
      KExceptionManager kem,
      Stopwatch sw) {
    this(
        kompileOptions,
        outerParsingOptions,
        innerParsingOptions,
        globalOptions,
        files,
        kem,
        sw,
        true);
  }

  public Kompile(
      KompileOptions kompileOptions,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      FileUtil files,
      KExceptionManager kem,
      Stopwatch sw,
      boolean cacheParses) {
    this.outerParsingOptions = outerParsingOptions;
    this.innerParsingOptions = innerParsingOptions;
    this.kompileOptions = kompileOptions;
    this.globalOptions = globalOptions;
    this.files = files;
    this.kem = kem;
    this.errors = new HashSet<>();
    this.parser = new ParserUtils(files, kem, kem.options, outerParsingOptions);
    List<File> lookupDirectories =
        this.outerParsingOptions.includes.stream()
            .map(files::resolveWorkingDirectory)
            .collect(Collectors.toList());
    // these directories should be relative to the current working directory if we refer to them
    // later after the WD has changed.
    this.outerParsingOptions.includes =
        lookupDirectories.stream().map(File::getAbsolutePath).collect(Collectors.toList());
    File cacheFile =
        kompileOptions.cacheFile != null
            ? files.resolveWorkingDirectory(kompileOptions.cacheFile)
            : files.resolveKompiled(CACHE_FILE_NAME);
    this.definitionParsing =
        new DefinitionParsing(
            lookupDirectories,
            kompileOptions,
            outerParsingOptions,
            innerParsingOptions,
            globalOptions,
            kem,
            files,
            parser,
            cacheParses,
            cacheFile,
            sw);
    this.sw = sw;
  }

  /**
   * Executes the Kompile tool. This tool accesses a
   *
   * @param definitionFile
   * @param mainModuleName
   * @param mainProgramsModuleName
   * @return
   */
  public CompiledDefinition run(
      File definitionFile,
      KompileOptions.MainModule mainModuleName,
      KompileOptions.SyntaxModule mainProgramsModuleName,
      Function<Definition, Definition> pipeline,
      Set<Att.Key> excludedModuleTags) {
    files.resolveKompiled(".").mkdirs();

    Definition parsedDef =
        parseDefinition(definitionFile, mainModuleName, mainProgramsModuleName, excludedModuleTags);

    files.saveToKompiled("parsed.txt", parsedDef.toString());
    preCompilationChecks(parsedDef, excludedModuleTags);
    sw.printIntermediate("Validate parsed definition");

    Definition kompiledDefinition = pipeline.apply(parsedDef);

    files.saveToKompiled("compiled.txt", kompiledDefinition.toString());
    postCompilationChecks(kompiledDefinition);
    sw.printIntermediate("Apply compile pipeline and validate definition");

    if (kompileOptions.postProcess != null) {
      kompiledDefinition = postProcessJSON(kompiledDefinition, kompileOptions.postProcess);
      files.saveToKompiled("post-processed.txt", kompiledDefinition.toString());
    }

    files.saveToKompiled("allRules.txt", ruleSourceMap(kompiledDefinition));

    if (kompileOptions.emitJson) {
      Stopwatch sw = new Stopwatch(globalOptions);
      files.saveToKompiled(
          "parsed.json", new String(ToJson.apply(parsedDef), StandardCharsets.UTF_8));
      files.saveToKompiled(
          "compiled.json", new String(ToJson.apply(kompiledDefinition), StandardCharsets.UTF_8));
      sw.printIntermediate("  Emit parsed & compiled JSON");
    }

    ConfigurationInfoFromModule configInfo =
        new ConfigurationInfoFromModule(kompiledDefinition.mainModule());

    Sort rootCell = Sorts.GeneratedTopCell();
    CompiledDefinition def =
        new CompiledDefinition(
            kompileOptions,
            kompileOptions.outerParsing,
            kompileOptions.innerParsing,
            globalOptions,
            parsedDef,
            kompiledDefinition,
            files,
            configInfo.getDefaultCell(rootCell).klabel());

    if (kompileOptions.genBisonParser || kompileOptions.genGlrBisonParser) {
      if (def.configurationVariableDefaultSorts.containsKey("$PGM")) {
        String filename =
            getBisonParserFilename(def.programStartSymbol.name(), def.mainSyntaxModuleName());
        File outputFile = files.resolveKompiled(filename);
        File linkFile = files.resolveKompiled("parser_PGM");
        new KRead(kem, files, InputModes.PROGRAM, globalOptions)
            .createBisonParser(
                def.programParsingModuleFor(def.mainSyntaxModuleName()).get(),
                def.programStartSymbol,
                outputFile,
                kompileOptions.genGlrBisonParser,
                kompileOptions.bisonFile,
                kompileOptions.bisonStackMaxDepth,
                kompileOptions.genBisonParserLibrary);
        try {
          linkFile.delete();
          Files.createSymbolicLink(
              linkFile.toPath(),
              files.resolveKompiled(".").toPath().relativize(outputFile.toPath()));
        } catch (IOException e) {
          throw KEMException.internalError("Cannot write to kompiled directory.", e);
        }
      }
      for (Production prod : iterable(kompiledDefinition.mainModule().productions())) {
        if (prod.att().contains(Att.CELL()) && prod.att().contains(Att.PARSER())) {
          String att = prod.att().get(Att.PARSER());
          String[][] parts = StringUtil.splitTwoDimensionalAtt(att);
          for (String[] part : parts) {
            if (part.length != 2) {
              throw KEMException.compilerError("Invalid value for parser attribute: " + att, prod);
            }
            String name = part[0];
            String module = part[1];
            Option<Module> mod = def.programParsingModuleFor(module);
            if (!mod.isDefined()) {
              throw KEMException.compilerError(
                  "Could not find module referenced by parser attribute: " + module, prod);
            }
            Sort sort = def.configurationVariableDefaultSorts.getOrDefault("$" + name, Sorts.K());
            String filename = getBisonParserFilename(sort.name(), module);
            File outputFile = files.resolveKompiled(filename);
            File linkFile = files.resolveKompiled("parser_" + name);
            new KRead(kem, files, InputModes.PROGRAM, globalOptions)
                .createBisonParser(
                    mod.get(),
                    sort,
                    outputFile,
                    kompileOptions.genGlrBisonParser,
                    null,
                    kompileOptions.bisonStackMaxDepth,
                    kompileOptions.genBisonParserLibrary);
            try {
              linkFile.delete();
              Files.createSymbolicLink(
                  linkFile.toPath(),
                  files.resolveKompiled(".").toPath().relativize(outputFile.toPath()));
            } catch (IOException e) {
              throw KEMException.internalError("Cannot write to kompiled directory.", e);
            }
          }
        }
      }
    }

    return def;
  }

  private String getBisonParserFilename(String sort, String module) {
    String baseName = "parser_" + sort + "_" + module;

    if (kompileOptions.genBisonParserLibrary) {
      return "lib" + baseName + OS.current().getSharedLibraryExtension();
    } else {
      return baseName;
    }
  }

  private Definition postProcessJSON(Definition defn, String postProcess) {
    List<String> command = new ArrayList<>(Arrays.asList(postProcess.split(" ")));
    Map<String, String> environment = new HashMap<>();
    File compiledJson;
    try {
      String inputDefinition = new String(ToJson.apply(defn), StandardCharsets.UTF_8);
      compiledJson = files.resolveTemp("post-process-compiled.json");
      FileUtils.writeStringToFile(compiledJson, inputDefinition);
    } catch (UnsupportedEncodingException e) {
      throw KEMException.criticalError("Could not encode definition to JSON!");
    } catch (IOException e) {
      throw KEMException.criticalError("Could not make temporary file!");
    }
    command.add(compiledJson.getAbsolutePath());
    RunProcess.ProcessOutput output =
        RunProcess.execute(
            environment, files.getProcessBuilder(), command.toArray(new String[command.size()]));
    sw.printIntermediate("Post process JSON: " + String.join(" ", command));
    if (output.exitCode() != 0) {
      throw KEMException.criticalError(
          "Post-processing returned a non-zero exit code: "
              + output.exitCode()
              + "\nStdout:\n"
              + new String(output.stdout())
              + "\nStderr:\n"
              + new String(output.stderr()));
    }
    return JsonParser.parseDefinition(new String(output.stdout()));
  }

  private static String ruleSourceMap(Definition def) {
    List<String> ruleLocs = new ArrayList<String>();
    for (Sentence s : JavaConverters.setAsJavaSet(def.mainModule().sentences())) {
      if (s instanceof RuleOrClaim) {
        var optFile = s.att().getOptional(Att.SOURCE(), Source.class);
        var optLine = s.att().getOptional(Att.LOCATION(), Location.class);
        var optCol = s.att().getOptional(Att.LOCATION(), Location.class);
        var optId = s.att().getOptional(Att.UNIQUE_ID());
        if (optFile.isPresent() && optLine.isPresent() && optCol.isPresent() && optId.isPresent()) {
          String file = optFile.get().source();
          int line = optLine.get().startLine();
          int col = optCol.get().startColumn();
          String loc = file + ":" + line + ":" + col;
          String id = optId.get();
          ruleLocs.add(id + " " + loc);
        }
      }
    }
    return String.join("\n", ruleLocs);
  }

  public Definition parseDefinition(
      File definitionFile,
      KompileOptions.MainModule mainModuleName,
      KompileOptions.SyntaxModule mainProgramsModule,
      Set<Att.Key> excludedModuleTags) {
    return definitionParsing.parseDefinitionAndResolveBubbles(
        definitionFile, mainModuleName, mainProgramsModule, excludedModuleTags);
  }

  private static Module filterStreamModules(Module input) {
    if (input.name().equals("STDIN-STREAM") || input.name().equals("STDOUT-STREAM")) {
      return Module(input.name(), Set(), Set(), input.att());
    }
    return input;
  }

  public static Definition resolveIOStreams(KExceptionManager kem, Definition d) {
    return DefinitionTransformer.from(new ResolveIOStreams(d, kem)::resolve, "resolving io streams")
        .andThen(DefinitionTransformer.from(Kompile::filterStreamModules, "resolving io streams"))
        .apply(d);
  }

  private static Module excludeModulesByTag(Set<Att.Key> excludedModuleTags, Module mod) {
    Predicate<Import> f =
        _import ->
            excludedModuleTags.stream().noneMatch(tag -> _import.module().att().contains(tag));
    Set<Import> newImports = stream(mod.imports()).filter(f).collect(Collectors.toSet());
    return Module(mod.name(), immutable(newImports), mod.localSentences(), mod.att());
  }

  private static Definition excludeModulesByTag(
      Set<Att.Key> excludedModuleTags, String syntaxModule, Definition d) {
    for (Att.Key k : excludedModuleTags) {
      if (d.mainModule().att().contains(k)) {
        throw KEMException.compilerError(
            "Main module " + d.mainModule().name() + " has excluded attribute [" + k + "].");
      }
      d.getModule(syntaxModule)
          .map(
              m -> {
                if (m.att().contains(k)) {
                  throw KEMException.compilerError(
                      "Syntax module " + m.name() + " has excluded attribute [" + k + "].");
                }
                return null;
              });
    }

    return Definition(
        d.mainModule(),
        immutable(
            stream(d.entryModules())
                .filter(
                    mod -> excludedModuleTags.stream().noneMatch(tag -> mod.att().contains(tag)))
                .collect(Collectors.toSet())),
        d.att());
  }

  public static Function1<Definition, Definition> excludeModulesByTag(
      Set<Att.Key> excludedModuleTags, String syntaxModule) {
    Function1<Definition, Definition> excludeModules =
        d -> excludeModulesByTag(excludedModuleTags, syntaxModule, d);
    DefinitionTransformer walkModules =
        DefinitionTransformer.from(
            mod -> excludeModulesByTag(excludedModuleTags, mod),
            "remove modules based on attributes");

    return excludeModules.andThen(walkModules);
  }

  public static Module subsortKItem(Module module) {
    java.util.Set<Sentence> prods = new HashSet<>();
    for (Sort srt : iterable(module.allSorts())) {
      if (!RuleGrammarGenerator.isParserSort(srt)) {
        // KItem ::= Sort
        Production prod = Production(Seq(), Sorts.KItem(), Seq(NonTerminal(srt)), Att.empty());
        if (!module.sentences().contains(prod)) {
          prods.add(prod);
        }
      }
    }
    if (prods.isEmpty()) {
      return module;
    } else {
      return Module(
          module.name(),
          module.imports(),
          immutable(
              Stream.concat(stream(module.sortedLocalSentences()), prods.stream())
                  .collect(Collectors.toSet())),
          module.att());
    }
  }

  public Rule parseAndCompileRule(
      CompiledDefinition compiledDef, String contents, Source source, Optional<Rule> parsedRule) {
    Rule parsed = parsedRule.orElseGet(() -> parseRule(compiledDef, contents, source));
    return compileRule(compiledDef.kompiledDefinition, parsed);
  }

  public Rule parseRule(CompiledDefinition compiledDef, String contents, Source source) {
    return definitionParsing.parseRule(compiledDef, contents, source);
  }

  private void preCompilationChecks(Definition parsedDef, Set<Att.Key> excludedModuleTags) {
    scala.collection.Set<Module> modules = parsedDef.modules();
    Module mainModule = parsedDef.mainModule();
    Option<Module> kModule = parsedDef.getModule("K");
    definitionChecks(stream(modules).collect(Collectors.toSet()));
    structuralChecks(modules, mainModule, kModule, excludedModuleTags);
  }

  /**
   * Run structural checks that rely on the compilation pipeline having already been run.
   *
   * <p>The checks run at this stage are:
   *
   * <ul>
   *   <li>Correctness of sorts: that there are no user-supplied parametric sorts remaining, and
   *       that all non-terminals have a valid sort assigned.
   *   <li>Validity of the overload lattice; running these checks requires that all
   *       compiler-generated subsort productions have been created.
   * </ul>
   *
   * @param def The definition to apply checks to.
   */
  private void postCompilationChecks(Definition def) {
    var modules = def.modules();
    var mainModule = def.mainModule();

    for (Module m : mutable(modules)) {
      m.checkSorts();
    }

    checkOverloads(mainModule);

    if (!errors.isEmpty()) {
      kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
      throw KEMException.compilerError("Had " + errors.size() + " errors after compilation.");
    }
  }

  // checks that are not verified in the prover
  public void definitionChecks(Set<Module> modules) {
    modules.forEach(
        m ->
            stream(m.sortedLocalSentences())
                .forEach(
                    s -> {
                      // Check that the `claim` keyword is not used in the definition.
                      if (s instanceof Claim)
                        errors.add(
                            KEMException.compilerError(
                                "Claims are not allowed in the definition.", s));
                    }));
  }

  // Extra checks just for the prover specification.
  public void proverChecksX(Module specModule, Module mainDefModule, boolean allowRules) {
    // check rogue syntax in spec module
    Set<Sentence> toCheck = mutable(specModule.sentences().$minus$minus(mainDefModule.sentences()));
    for (Sentence s : toCheck)
      if (s.isSyntax()
          && (!s.att().contains(Att.TOKEN())
              || !mainDefModule.allSorts().contains(((Production) s).sort())))
        errors.add(
            KEMException.compilerError(
                "Found syntax declaration in proof module. Only tokens for existing sorts are"
                    + " allowed.",
                s));

    ModuleTransformer mt =
        ModuleTransformer.fromSentenceTransformer(
            (m, s) -> {
              if (m.name().equals(mainDefModule.name())
                  || mainDefModule.importedModuleNames().contains(m.name())) return s;
              if (!(s instanceof Claim || s.isSyntax())) {
                if (s instanceof Rule && !allowRules && !s.att().contains(Att.SIMPLIFICATION()))
                  errors.add(
                      KEMException.compilerError(
                          "Only claims and simplification rules are allowed in proof modules.", s));
              }
              return s;
            },
            "rules in spec module");
    mt.apply(specModule);
  }

  public void structuralChecks(
      scala.collection.Set<Module> modules,
      Module mainModule,
      Option<Module> kModule,
      Set<Att.Key> excludedModuleTags) {
    checkAnywhereRules(modules);

    boolean isSymbolic = excludedModuleTags.contains(Att.CONCRETE());
    CheckRHSVariables checkRHSVariables =
        new CheckRHSVariables(errors, !isSymbolic, kompileOptions.backend);
    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(checkRHSVariables::check));

    stream(modules).forEach(m -> new CheckAtt(errors, kem, m).check());

    stream(modules)
        .forEach(
            m ->
                stream(m.sortedLocalSentences())
                    .forEach(new CheckConfigurationCells(errors, m)::check));

    stream(modules)
        .forEach(
            m ->
                stream(m.sortedLocalSentences())
                    .forEach(new CheckSortTopUniqueness(errors, m)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckStreams(errors, m)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckRewrite(errors, m)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckHOLE(errors, m)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckTokens(errors, m)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckK(errors)::check));

    stream(modules)
        .forEach(
            m -> stream(m.sortedLocalSentences()).forEach(new CheckFunctions(errors, m)::check));

    stream(modules)
        .forEach(
            m -> stream(m.sortedLocalSentences()).forEach(new CheckAnonymous(errors, kem)::check));

    stream(modules)
        .forEach(
            m ->
                stream(m.sortedLocalSentences())
                    .forEach(new CheckSyntaxGroups(errors, m, kem)::check));

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckAssoc(errors, m)::check));

    stream(modules)
        .forEach(
            m -> stream(m.sortedLocalSentences()).forEach(new CheckDeprecated(errors, kem)::check));

    Set<String> moduleNames = new HashSet<>();
    stream(modules)
        .forEach(
            m -> {
              if (moduleNames.contains(m.name())) {
                errors.add(
                    KEMException.compilerError("Found multiple modules with name: " + m.name()));
              }
              moduleNames.add(m.name());
            });

    CheckKLabels checkKLabels = new CheckKLabels(errors, kem, files);
    Set<String> checkedModules = new HashSet<>();
    // only check imported modules because otherwise we might have false positives
    Consumer<Module> checkModuleKLabels =
        m -> {
          if (!checkedModules.contains(m.name())) {
            stream(m.sortedLocalSentences()).forEach(s -> checkKLabels.check(s, m));
          }
          checkedModules.add(m.name());
        };

    if (kModule.nonEmpty()) {
      stream(kModule.get().importedModules()).forEach(checkModuleKLabels);
      checkModuleKLabels.accept(kModule.get());
    }
    stream(mainModule.importedModules()).forEach(checkModuleKLabels);
    checkModuleKLabels.accept(mainModule);
    checkKLabels.check(mainModule);

    stream(modules)
        .forEach(m -> stream(m.sortedLocalSentences()).forEach(new CheckLabels(errors)::check));

    checkIsSortPredicates(modules);

    if (!errors.isEmpty()) {
      kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
      throw KEMException.compilerError("Had " + errors.size() + " structural errors.");
    }
  }

  private void checkSingletonOverload(Module module) {
    // When disambiguating, an extra production `Es ::= E` is added for every user list
    // sort `Es`.
    //
    // This means that productions that reference a user list sort (or the child sort of
    // one) can behave as overloads at disambiguation, even if they look like singletons
    // from the perspective. We therefore need to use the disambiguation module to implement this
    // check.
    //
    // See `RuleGrammarGenerator::getCombinedGrammarImpl`.
    var disambMod = RuleGrammarGenerator.getCombinedGrammarImpl(module, false, false, true)._2();
    scala.collection.immutable.Seq<Production> withOverload =
        disambMod.productions().filter(p -> p.att().contains(Att.OVERLOAD())).toSeq();

    stream(withOverload)
        .forEach(
            p -> {
              if (!disambMod.overloads().elements().contains(p)) {
                kem.registerCompilerWarning(
                    KException.ExceptionType.SINGLETON_OVERLOAD,
                    errors,
                    "Production has an `overload(_)` attribute but is not an overload of any other production.",
                    p);
              }
            });
  }

  private void checkDuplicateOverloads(Module module) {
    // Group the overloaded productions in this module by their `overload(_)` attribute, then
    // examine each group to see if the elements in that group are connected. If elements with the
    // same attribute are not in the same connected component, then we have two disjoint overload
    // sets with the same name, which is potentially confusing to the user.
    var attributeGroups =
        module.overloads().elements().stream()
            .filter(p -> p.att().contains(Att.OVERLOAD()))
            .collect(Collectors.groupingBy(p -> p.att().get(Att.OVERLOAD())))
            .values();
    attributeGroups.forEach(
        l ->
            l.sort(
                (p1, p2) ->
                    Comparators.<Location>emptiesLast(Comparator.naturalOrder())
                        .compare(p1.location(), p2.location())));

    attributeGroups.forEach(
        ps -> {
          var userList = ps.stream().allMatch(p -> p.att().contains(Att.USER_LIST()));

          var groups =
              ps.stream()
                  .collect(Collectors.groupingBy(module.overloads().connectedComponents()::get));

          if (groups.size() > (userList ? 2 : 1)) {
            for (var g : groups.values()) {
              assert !g.isEmpty();
              var prod = g.get(0);
              var key = prod.att().get(Att.OVERLOAD());
              kem.registerCompilerWarning(
                  KException.ExceptionType.DUPLICATE_OVERLOAD,
                  errors,
                  "Overload `"
                      + key
                      + "` is not unique. Consider renaming one of the overload sets with this key.",
                  prod);
            }
          }
        });
  }

  private void checkOverloads(Module module) {
    checkSingletonOverload(module);
    checkDuplicateOverloads(module);
  }

  private void checkAnywhereRules(scala.collection.Set<Module> modules) {
    if (kompileOptions.backend.equals(Backends.HASKELL)
        && !kompileOptions.allowAnywhereRulesHaskell) {
      errors.addAll(
          stream(modules)
              .flatMap(
                  m ->
                      stream(m.sortedLocalSentences())
                          .flatMap(
                              s -> {
                                if (s instanceof Rule && s.att().contains(Att.ANYWHERE()))
                                  return Stream.of(
                                      KEMException.compilerError(
                                          Att.ANYWHERE()
                                              + " is not supported by the "
                                              + Backends.HASKELL
                                              + " backend.",
                                          s));
                                return Stream.empty();
                              }))
              .collect(Collectors.toSet()));
    }
  }

  private void checkIsSortPredicates(scala.collection.Set<Module> modules) {
    Set<String> generatedIsSorts =
        stream(modules)
            .flatMap(m -> stream(m.definedSorts()))
            .map(s -> "is" + s.toString())
            .collect(Collectors.toSet());

    stream(modules)
        .flatMap(
            m -> stream(optional(m.productionsForSort().get(Sorts.Bool().head())).orElse(Set())))
        .collect(Collectors.toSet())
        .forEach(
            prod -> {
              scala.collection.immutable.Seq<ProductionItem> items = prod.items();
              if (items.size() < 3) {
                return;
              }
              ProductionItem first = items.head();
              ProductionItem second = items.apply(1);
              ProductionItem last = items.last();
              // Check if the production is of the form isSort ( ... )
              if ((first instanceof Terminal)
                  && (second instanceof Terminal)
                  && (last instanceof Terminal)
                  && generatedIsSorts.contains(((Terminal) first).value())
                  && ((Terminal) second).value().equals("(")
                  && ((Terminal) last).value().equals(")")) {
                errors.add(
                    KEMException.compilerError(
                        "Syntax declaration conflicts with automatically generated "
                            + ((Terminal) first).value()
                            + " predicate.",
                        prod));
              }
            });
  }

  public static Definition addSemanticsModule(Definition d) {
    java.util.Set<Module> allModules = mutable(d.modules());

    Module languageParsingModule =
        Constructors.Module(
            "LANGUAGE-PARSING",
            Set(
                Import(d.mainModule(), true),
                Import(d.getModule(d.att().get(Att.SYNTAX_MODULE())).get(), true),
                Import(d.getModule("K-TERM").get(), true),
                Import(d.getModule(RuleGrammarGenerator.ID_PROGRAM_PARSING).get(), true)),
            Set(),
            Att.empty());
    allModules.add(languageParsingModule);
    return Constructors.Definition(d.mainModule(), immutable(allModules), d.att());
  }

  public Rule compileRule(Definition compiledDef, Rule parsedRule) {
    return (Rule)
        UnaryOperator.<Sentence>identity()
            .andThen(new ResolveAnonVar()::resolve)
            .andThen(new ResolveSemanticCasts(false)::resolve)
            .andThen(s -> concretizeSentence(s, compiledDef))
            .apply(parsedRule);
  }

  public Set<Module> parseModules(
      CompiledDefinition definition,
      KompileOptions.MainModule mainModule,
      String entryPointModule,
      File definitionFile,
      Set<Att.Key> excludedModuleTags,
      boolean readOnlyCache,
      boolean useCachedScanner) {
    Set<Module> modules =
        definitionParsing.parseModules(
            definition,
            mainModule,
            entryPointModule,
            definitionFile,
            excludedModuleTags,
            readOnlyCache,
            useCachedScanner);
    int totalBubbles =
        definitionParsing.parsedBubbles.get() + definitionParsing.cachedBubbles.get();
    sw.printIntermediate(
        "Parse spec modules ["
            + definitionParsing.parsedBubbles.get()
            + "/"
            + totalBubbles
            + " rules]");
    return modules;
  }

  private Sentence concretizeSentence(Sentence s, Definition input) {
    ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
    LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
    SortInfo sortInfo = SortInfo.fromModule(input.mainModule());
    return new ConcretizeCells(configInfo, labelInfo, sortInfo, input.mainModule())
        .concretize(input.mainModule(), s);
  }
}
