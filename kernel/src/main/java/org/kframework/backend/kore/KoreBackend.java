// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.kore;

import static org.kframework.Collections.*;

import com.google.inject.Inject;
import java.io.File;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import org.apache.commons.io.FilenameUtils;
import org.kframework.Strategy;
import org.kframework.attributes.Att;
import org.kframework.backend.Backend;
import org.kframework.backend.Backends;
import org.kframework.compile.*;
import org.kframework.compile.passes.AddCoolLikeAtt;
import org.kframework.compile.passes.AddImplicitComputationCell;
import org.kframework.compile.passes.AddImplicitCounterCell;
import org.kframework.compile.passes.AddSortInjections;
import org.kframework.compile.passes.ConcretizeCells;
import org.kframework.compile.passes.ConstantFolding;
import org.kframework.compile.passes.ExpandMacros;
import org.kframework.compile.passes.GenerateCoverage;
import org.kframework.compile.passes.GenerateSortPredicateRules;
import org.kframework.compile.passes.GenerateSortPredicateSyntax;
import org.kframework.compile.passes.GenerateSortProjections;
import org.kframework.compile.passes.GuardOrPatterns;
import org.kframework.compile.passes.MarkExtraConcreteRules;
import org.kframework.compile.passes.MinimizeTermConstruction;
import org.kframework.compile.passes.NumberSentences;
import org.kframework.compile.passes.PropagateMacro;
import org.kframework.compile.passes.RemoveUnit;
import org.kframework.compile.passes.ResolveAnonVar;
import org.kframework.compile.passes.ResolveComm;
import org.kframework.compile.passes.ResolveContexts;
import org.kframework.compile.passes.ResolveFreshConfigConstants;
import org.kframework.compile.passes.ResolveFreshConstants;
import org.kframework.compile.passes.ResolveFun;
import org.kframework.compile.passes.ResolveFunctionWithConfig;
import org.kframework.compile.passes.ResolveHeatCoolAttribute;
import org.kframework.compile.passes.ResolveSemanticCasts;
import org.kframework.compile.passes.ResolveStrict;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.KLabel;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;

public class KoreBackend implements Backend {

  private final KompileOptions kompileOptions;
  protected final FileUtil files;
  private final KExceptionManager kem;
  protected final boolean heatCoolEquations;
  private final Tool tool;

  @Inject
  public KoreBackend(
      KompileOptions kompileOptions, FileUtil files, KExceptionManager kem, Tool tool) {
    this(kompileOptions, files, kem, false, tool);
  }

  public KoreBackend(
      KompileOptions kompileOptions,
      FileUtil files,
      KExceptionManager kem,
      boolean heatCoolEquations,
      Tool tool) {
    this.kompileOptions = kompileOptions;
    this.files = files;
    this.kem = kem;
    this.heatCoolEquations = heatCoolEquations;
    this.tool = tool;
  }

  @Override
  public void accept(Backend.Holder h) {
    CompiledDefinition def = h.def;
    String kore = getKompiledString(def);
    File defFile = kompileOptions.outerParsing.mainDefinitionFile(files);
    String name = defFile.getName();
    String basename = FilenameUtils.removeExtension(name);
    files.saveToDefinitionDirectory(basename + ".kore", kore);
  }

  /** Convert a CompiledDefinition to a String of a KORE definition. */
  protected String getKompiledString(CompiledDefinition def) {
    Module mainModule = getKompiledModule(def.kompiledDefinition.mainModule());
    ModuleToKORE converter =
        new ModuleToKORE(mainModule, def.topCellInitializer, def.kompileOptions);
    return getKompiledString(converter, files, heatCoolEquations, tool);
  }

  public static String getKompiledString(
      ModuleToKORE converter, FileUtil files, boolean heatCoolEquations, Tool t) {
    return getKompiledStringAndWriteSyntaxMacros(
        converter, files, heatCoolEquations, new StringBuilder(), t);
  }

  public static String getKompiledStringAndWriteSyntaxMacros(
      ModuleToKORE converter, FileUtil files, boolean heatCoolEq, StringBuilder sb, Tool t) {
    StringBuilder semantics = new StringBuilder();
    StringBuilder syntax = new StringBuilder();
    StringBuilder macros = new StringBuilder();
    String prelude = files.loadFromKIncludeDir("kore/prelude.kore");
    converter.convert(heatCoolEq, prelude, semantics, syntax, macros);
    if (t == Tool.KOMPILE) {
      files.saveToKompiled("syntaxDefinition.kore", syntax.toString());
      files.saveToKompiled("macros.kore", macros.toString());
    }
    return semantics.toString();
  }

  public static Module getKompiledModule(Module mainModule) {
    mainModule =
        ModuleTransformer.fromSentenceTransformer(
                new AddSortInjections(mainModule)::addInjections, "Add sort injections")
            .apply(mainModule);
    mainModule =
        ModuleTransformer.from(new RemoveUnit()::apply, "Remove unit applications for collections")
            .apply(mainModule);
    mainModule =
        ModuleTransformer.fromSentenceTransformer(
                new MinimizeTermConstruction(mainModule)::resolve, "Minimize term construction")
            .apply(mainModule);
    return mainModule;
  }

  @Override
  public Function<Definition, Definition> steps() {
    DefinitionTransformer resolveComm =
        DefinitionTransformer.from(
            new ResolveComm(kem)::resolve, "resolve comm simplification rules");
    Function1<Definition, Definition> resolveStrict =
        d ->
            DefinitionTransformer.from(
                    new ResolveStrict(kompileOptions, d)::resolve,
                    "resolving strict and seqstrict attributes")
                .apply(d);
    DefinitionTransformer resolveHeatCoolAttribute =
        DefinitionTransformer.fromSentenceTransformer(
            new ResolveHeatCoolAttribute(new HashSet<>())::resolve,
            "resolving heat and cool attributes");
    DefinitionTransformer resolveAnonVars =
        DefinitionTransformer.fromSentenceTransformer(
            new ResolveAnonVar()::resolve, "resolving \"_\" vars");
    DefinitionTransformer guardOrs =
        DefinitionTransformer.fromSentenceTransformer(
            new GuardOrPatterns()::resolve, "resolving or patterns");
    DefinitionTransformer resolveSemanticCasts =
        DefinitionTransformer.fromSentenceTransformer(
            new ResolveSemanticCasts(true)::resolve, "resolving semantic casts");
    DefinitionTransformer resolveFun =
        DefinitionTransformer.from(new ResolveFun()::resolve, "resolving #fun");
    Function1<Definition, Definition> resolveFunctionWithConfig =
        d ->
            DefinitionTransformer.from(
                    new ResolveFunctionWithConfig(d)::moduleResolve,
                    "resolving functions with config context")
                .apply(d);
    DefinitionTransformer generateSortPredicateSyntax =
        DefinitionTransformer.from(
            new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");
    DefinitionTransformer generateSortPredicateRules =
        DefinitionTransformer.from(
            new GenerateSortPredicateRules()::gen, "adding sort predicate rules");
    DefinitionTransformer generateSortProjections =
        DefinitionTransformer.from(
            new GenerateSortProjections(kompileOptions.coverage)::gen, "adding sort projections");
    DefinitionTransformer subsortKItem =
        DefinitionTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
    Function1<Definition, Definition> addCoolLikeAtt =
        d ->
            DefinitionTransformer.fromSentenceTransformer(
                    new AddCoolLikeAtt(d.mainModule())::add, "add cool-like attribute")
                .apply(d);
    Function1<Definition, Definition> propagateMacroToRules =
        d ->
            DefinitionTransformer.fromSentenceTransformer(
                    (m, s) -> new PropagateMacro(m).propagate(s),
                    "propagate macro labels from production to rules")
                .apply(d);
    Function1<Definition, Definition> expandMacros =
        d -> {
          ResolveFunctionWithConfig transformer = new ResolveFunctionWithConfig(d);
          return DefinitionTransformer.fromSentenceTransformer(
                  (m, s) ->
                      new ExpandMacros(transformer, m, files, kem, kompileOptions, false).expand(s),
                  "expand macros")
              .apply(d);
        };
    Function1<Definition, Definition> checkSimplificationRules =
        d ->
            DefinitionTransformer.from(
                    m -> {
                      m.localRules().foreach(r -> checkSimpIsFunc(m, r));
                      return m;
                    },
                    "Check simplification rules")
                .apply(d);
    DefinitionTransformer constantFolding =
        DefinitionTransformer.fromSentenceTransformer(
            new ConstantFolding()::fold, "constant expression folding");
    ResolveFreshConfigConstants freshConfigResolver = new ResolveFreshConfigConstants();
    Function1<Definition, Definition> resolveFreshConfigConstants =
        d ->
            DefinitionTransformer.from(
                    m -> freshConfigResolver.resolve(m), "resolving !Var config variables")
                .apply(d);
    Function1<Definition, Definition> resolveFreshConstants =
        d ->
            DefinitionTransformer.from(
                    m ->
                        new ResolveFreshConstants(
                                d,
                                kompileOptions.topCell,
                                files,
                                freshConfigResolver.getCurrentFresh())
                            .resolve(m),
                    "resolving !Var variables")
                .apply(d);
    GenerateCoverage cov = new GenerateCoverage(kompileOptions.coverage, files);
    Function1<Definition, Definition> genCoverage =
        d ->
            DefinitionTransformer.fromRuleBodyTransformerWithRule(
                    (r, body) -> cov.gen(r, body, d.mainModule()),
                    "generate coverage instrumentation")
                .apply(d);
    DefinitionTransformer numberSentences =
        DefinitionTransformer.fromSentenceTransformer(
            NumberSentences::number, "number sentences uniquely");
    Function1<Definition, Definition> resolveConfigVar =
        d ->
            DefinitionTransformer.fromSentenceTransformer(
                    new ResolveFunctionWithConfig(d)::resolveConfigVar,
                    "Adding configuration variable to lhs")
                .apply(d);
    Function1<Definition, Definition> resolveIO = (d -> Kompile.resolveIOStreams(kem, d));
    Function1<Definition, Definition> markExtraConcreteRules =
        d -> MarkExtraConcreteRules.mark(d, kompileOptions.extraConcreteRuleLabels);
    Function1<Definition, Definition> removeAnywhereRules =
        d ->
            DefinitionTransformer.from(
                    this::removeAnywhereRules, "removing anywhere rules for the Haskell backend")
                .apply(d);

    return def ->
        resolveComm
            .andThen(resolveIO)
            .andThen(resolveFun)
            .andThen(resolveFunctionWithConfig)
            .andThen(resolveStrict)
            .andThen(resolveAnonVars)
            .andThen(d -> new ResolveContexts(kompileOptions).resolve(d))
            .andThen(numberSentences)
            .andThen(resolveHeatCoolAttribute)
            .andThen(resolveSemanticCasts)
            .andThen(subsortKItem)
            .andThen(generateSortPredicateSyntax)
            .andThen(generateSortProjections)
            .andThen(constantFolding)
            .andThen(propagateMacroToRules)
            .andThen(expandMacros)
            .andThen(checkSimplificationRules)
            .andThen(guardOrs)
            .andThen(AddImplicitComputationCell::transformDefinition)
            .andThen(resolveFreshConfigConstants)
            .andThen(resolveFreshConstants)
            .andThen(generateSortPredicateSyntax)
            .andThen(generateSortProjections)
            .andThen(subsortKItem)
            .andThen(d -> new Strategy().addStrategyCellToRulesTransformer(d).apply(d))
            .andThen(d -> Strategy.addStrategyRuleToMainModule(def.mainModule().name()).apply(d))
            .andThen(d -> ConcretizeCells.transformDefinition(d))
            .andThen(genCoverage)
            .andThen(Kompile::addSemanticsModule)
            .andThen(resolveConfigVar)
            .andThen(addCoolLikeAtt)
            .andThen(markExtraConcreteRules)
            .andThen(removeAnywhereRules)
            .andThen(generateSortPredicateRules)
            .andThen(numberSentences)
            .apply(def);
  }

  ModuleTransformer resolveComm() {
    return ModuleTransformer.from(
        new ResolveComm(kem)::resolve, "resolve comm simplification rules");
  }

  ModuleTransformer resolveAnonVars() {
    return ModuleTransformer.fromSentenceTransformer(
        new ResolveAnonVar()::resolve, "resolving \"_\" vars");
  }

  ModuleTransformer addImplicitCounterCell() {
    return ModuleTransformer.fromSentenceTransformer(
        new AddImplicitCounterCell()::apply, "adding <generatedCounter> to claims if necessary");
  }

  ModuleTransformer numberSentences() {
    return ModuleTransformer.fromSentenceTransformer(
        NumberSentences::number, "number sentences uniquely");
  }

  ModuleTransformer resolveSemanticCasts() {
    return ModuleTransformer.fromSentenceTransformer(
        new ResolveSemanticCasts(true)::resolve, "resolving semantic casts");
  }

  ModuleTransformer generateSortProjections() {
    return ModuleTransformer.from(
        new GenerateSortProjections(false)::gen, "adding sort projections");
  }

  ModuleTransformer propagateMacroToRules() {
    return ModuleTransformer.fromSentenceTransformer(
        (m, s) -> new PropagateMacro(m).propagate(s),
        "propagate macro labels from production to rules");
  }

  ModuleTransformer expandMacros(ResolveFunctionWithConfig transformer) {
    return ModuleTransformer.fromSentenceTransformer(
        (m, s) -> new ExpandMacros(transformer, m, files, kem, kompileOptions, false).expand(s),
        "expand macros");
  }

  ModuleTransformer checkSimplificationRules() {
    return ModuleTransformer.from(
        m -> {
          m.localRules().foreach(r -> checkSimpIsFunc(m, r));
          return m;
        },
        "Check simplification rules");
  }

  ModuleTransformer addImplicitComputationCell(
      ConfigurationInfoFromModule configInfo, LabelInfo labelInfo) {
    return ModuleTransformer.fromSentenceTransformer(
        new AddImplicitComputationCell(configInfo, labelInfo)::apply, "concretizing configuration");
  }

  ModuleTransformer resolveFreshConstants(Definition def) {
    return ModuleTransformer.from(
        new ResolveFreshConstants(def, kompileOptions.topCell, files)::resolve,
        "resolving !Var variables");
  }

  ModuleTransformer concretizeCells(
      Module mod, ConfigurationInfoFromModule configInfo, LabelInfo labelInfo, SortInfo sortInfo) {
    return ModuleTransformer.fromSentenceTransformer(
        new ConcretizeCells(configInfo, labelInfo, sortInfo, mod)::concretize,
        "concretizing configuration");
  }

  ModuleTransformer subsortKItem() {
    return ModuleTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
  }

  ModuleTransformer restoreDefinitionModules(Definition def) {
    return ModuleTransformer.from(
        mod -> def.getModule(mod.name()).isDefined() ? def.getModule(mod.name()).get() : mod,
        "restore definition modules to same state as in definition");
  }

  @Override
  public Function<Module, Module> specificationSteps(Definition def) {
    var mp = new ModulePipeline();

    Module mod = def.mainModule();
    ResolveFunctionWithConfig transformer = new ResolveFunctionWithConfig(def);
    ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(mod);
    LabelInfo labelInfo = new LabelInfoFromModule(mod);
    SortInfo sortInfo = SortInfo.fromModule(mod);

    mp.add(resolveComm());
    mp.add(addImplicitCounterCell());
    mp.add(resolveAnonVars());
    mp.add(numberSentences());
    mp.add(resolveSemanticCasts());
    mp.add(generateSortProjections());
    mp.add(propagateMacroToRules());
    mp.add(expandMacros(transformer));
    mp.add(checkSimplificationRules());
    mp.add(addImplicitComputationCell(configInfo, labelInfo));
    mp.add(resolveFreshConstants(def));
    mp.add(concretizeCells(mod, configInfo, labelInfo, sortInfo));
    mp.add(subsortKItem());
    mp.add(restoreDefinitionModules(def));
    mp.add(numberSentences());

    return mp::apply;
  }

  // check that simplification rules have a functional symbol on the LHS
  public Sentence checkSimpIsFunc(Module m, Sentence s) {
    // need to check after macro expansion
    if (s instanceof Rule && (s.att().contains(Att.SIMPLIFICATION()))) {
      KLabel kl = m.matchKLabel((Rule) s);
      Att atts = m.attributesFor().get(kl).getOrElse(Att::empty);
      if (!(atts.contains(Att.FUNCTION())
          || atts.contains(Att.FUNCTIONAL())
          || atts.contains(Att.ML_OP())))
        throw KEMException.compilerError(
            "Simplification rules expect function/functional/mlOp symbols at the top of the left"
                + " hand side term.",
            s);
    }
    return s;
  }

  /**
   * If a user guarantees that their semantics will never _dynamically_ try to rewrite an anywhere
   * rule on the Haskell backend (with the --allow-anywhere-haskell flag), but cannot prove this
   * statically, we allow them to strip out all those rules before sending the definition to the
   * backend. If this transformation is applied unsoundly (i.e. an anywhere rule would have been
   * attempted if it had not been stripped), the behaviour of the Haskell backend on that program is
   * essentially undefined.
   */
  private Module removeAnywhereRules(Module m) {
    java.util.Set<Sentence> sentences = mutable(m.localSentences());

    if (kompileOptions.backend.equals(Backends.HASKELL)
        && kompileOptions.allowAnywhereRulesHaskell) {
      java.util.Set<Sentence> filtered = new HashSet<Sentence>();

      for (var s : sentences) {
        if (s instanceof Rule && s.att().contains(Att.ANYWHERE())) {
          kem.registerCompilerWarning(
              KException.ExceptionType.REMOVED_ANYWHERE,
              "Removed anywhere rule for Haskell backend execution; this may change the behavior of"
                  + " your code.",
              s);
        } else {
          filtered.add(s);
        }
      }

      sentences = filtered;
    }
    return new Module(m.name(), m.imports(), immutable(sentences), m.att());
  }

  @Override
  public Set<Att.Key> excludedModuleTags() {
    return Collections.singleton(Att.SYMBOLIC());
  }
}
