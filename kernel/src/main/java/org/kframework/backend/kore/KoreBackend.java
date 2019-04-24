// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.Strategy;
import org.kframework.compile.AddImplicitComputationCell;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.Backend;
import org.kframework.compile.ConcretizeCells;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.GeneratedTopFormat;
import org.kframework.compile.GenerateSortPredicateRules;
import org.kframework.compile.GenerateSortPredicateSyntax;
import org.kframework.compile.GenerateSortProjections;
import org.kframework.compile.GuardOrPatterns;
import org.kframework.compile.LabelInfo;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.compile.MinimizeTermConstruction;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.compile.ResolveContexts;
import org.kframework.compile.ResolveFreshConstants;
import org.kframework.compile.ResolveFun;
import org.kframework.compile.ResolveFunctionWithConfig;
import org.kframework.compile.ResolveHeatCoolAttribute;
import org.kframework.compile.ResolveSemanticCasts;
import org.kframework.compile.ResolveStrict;
import org.kframework.compile.SortInfo;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import scala.Function1;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Properties;
import java.util.Set;
import java.util.function.Function;

import static org.kframework.compile.ResolveHeatCoolAttribute.Mode.*;

public class KoreBackend implements Backend {

    private final KompileOptions kompileOptions;
    protected final FileUtil files;
    private final KExceptionManager kem;
    private final EnumSet<ResolveHeatCoolAttribute.Mode> heatCoolConditions;
    private final boolean heatCoolEquations;

    @Inject
    public KoreBackend(
            KompileOptions kompileOptions,
            FileUtil files,
            KExceptionManager kem) {
        this(kompileOptions, files, kem, EnumSet.of(HEAT_RESULT), false);
    }

    public KoreBackend(KompileOptions kompileOptions, FileUtil files, KExceptionManager kem, EnumSet<ResolveHeatCoolAttribute.Mode> heatCoolConditions, boolean heatCoolEquations) {
        this.kompileOptions = kompileOptions;
        this.files = files;
        this.kem = kem;
        this.heatCoolConditions = heatCoolConditions;
        this.heatCoolEquations = heatCoolEquations;
    }

    @Override
    public void accept(CompiledDefinition def) {
        String kore = getKompiledString(def);
        File defFile = kompileOptions.outerParsing.mainDefinitionFile(files);
        String name = defFile.getName();
        String basename = FilenameUtils.removeExtension(name);
        files.saveToDefinitionDirectory(basename + ".kore", kore);
    }

    protected String getKompiledString(CompiledDefinition def) {
        return getKompiledString(def.kompiledDefinition.mainModule(), def.topCellInitializer, files, heatCoolEquations);
    }

    public static String getKompiledString(Module mainModule, KLabel topCellInitializer, FileUtil files, boolean heatCoolEquations) {
        mainModule = new GenerateSortPredicateRules(true).gen(mainModule);
        mainModule = ModuleTransformer.fromSentenceTransformer(new AddSortInjections(mainModule)::addInjections, "Add sort injections").apply(mainModule);
        mainModule = ModuleTransformer.fromSentenceTransformer(new MinimizeTermConstruction(mainModule)::resolve, "Minimize term construction").apply(mainModule);
        ModuleToKORE moduleToKORE = new ModuleToKORE(mainModule, files, topCellInitializer);
        String kompiledString = moduleToKORE.convert(heatCoolEquations);
        Properties koreToKLabels = new Properties();
        koreToKLabels.putAll(moduleToKORE.getKToKoreLabelMap().inverse());
        try {
            FileOutputStream output = new FileOutputStream(files.resolveKompiled("kore_to_k_labels.properties"));
            koreToKLabels.store(output, "Properties file containing the mapping from kore to k labels");

        } catch (IOException e) {
            throw KEMException.criticalError("Error while saving kore to K labels map", e);
        }
        return kompiledString;
    }

    @Override
    public Function<Definition, Definition> steps() {
        DefinitionTransformer resolveStrict = DefinitionTransformer.from(new ResolveStrict(kompileOptions)::resolve, "resolving strict and seqstrict attributes");
        DefinitionTransformer resolveHeatCoolAttribute = DefinitionTransformer.fromSentenceTransformer(new ResolveHeatCoolAttribute(new HashSet<>(kompileOptions.transition), heatCoolConditions)::resolve, "resolving heat and cool attributes");
        DefinitionTransformer resolveAnonVars = DefinitionTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolving \"_\" vars");
        DefinitionTransformer guardOrs = DefinitionTransformer.fromSentenceTransformer(new GuardOrPatterns(true)::resolve, "resolving or patterns");
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(true)::resolve, "resolving semantic casts");
        DefinitionTransformer resolveFun = DefinitionTransformer.from(new ResolveFun()::resolve, "resolving #fun");
        DefinitionTransformer resolveFunctionWithConfig = DefinitionTransformer.fromSentenceTransformer(new ResolveFunctionWithConfig()::resolve, "resolving functions with config context");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");
        DefinitionTransformer generateSortProjections = DefinitionTransformer.from(new GenerateSortProjections()::gen, "adding sort projections");
        DefinitionTransformer subsortKItem = DefinitionTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
        DefinitionTransformer expandMacros = DefinitionTransformer.fromSentenceTransformer((m, s) -> new ExpandMacros(m, files, kompileOptions, false).expand(s), "expand macros");
        Function1<Definition, Definition> resolveFreshConstants = d -> DefinitionTransformer.from(m -> GeneratedTopFormat.resolve(new ResolveFreshConstants(d, true).resolve(m)), "resolving !Var variables").apply(d);
        DefinitionTransformer resolveConfigVar = DefinitionTransformer.fromSentenceTransformer(new ResolveFunctionWithConfig()::resolveConfigVar, "Adding configuration variable to lhs");
        Function1<Definition, Definition> resolveIO = (d -> Kompile.resolveIOStreams(kem, d));

        return def -> resolveIO
                .andThen(resolveFunctionWithConfig)
                .andThen(resolveFun)
                .andThen(resolveStrict)
                .andThen(resolveAnonVars)
                .andThen(d -> new ResolveContexts(kompileOptions).resolve(d))
                .andThen(resolveHeatCoolAttribute)
                .andThen(resolveSemanticCasts)
                .andThen(subsortKItem)
                .andThen(expandMacros)
                .andThen(guardOrs)
                .andThen(generateSortPredicateSyntax)
                .andThen(generateSortProjections)
                .andThen(AddImplicitComputationCell::transformDefinition)
                .andThen(resolveFreshConstants)
                .andThen(d -> new Strategy(kompileOptions.experimental.heatCoolStrategies).addStrategyCellToRulesTransformer(d).apply(d))
                .andThen(d -> Strategy.addStrategyRuleToMainModule(def.mainModule().name()).apply(d))
                .andThen(ConcretizeCells::transformDefinition)
                .andThen(Kompile::addSemanticsModule)
                .andThen(resolveConfigVar)
                .apply(def);
    }

    @Override
    public Function<Module, Module> specificationSteps(Definition def) {
        Module mod = def.mainModule();
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(mod);
        LabelInfo labelInfo = new LabelInfoFromModule(mod);
        SortInfo sortInfo = SortInfo.fromModule(mod);
        ModuleTransformer resolveAnonVars = ModuleTransformer.fromSentenceTransformer(
                new ResolveAnonVar()::resolve,
                "resolving \"_\" vars");
        ModuleTransformer resolveSemanticCasts = ModuleTransformer.fromSentenceTransformer(
                new ResolveSemanticCasts(true)::resolve,
                "resolving semantic casts");
        ModuleTransformer subsortKItem = ModuleTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
        ModuleTransformer addImplicitComputationCell = ModuleTransformer.fromSentenceTransformer(
                new AddImplicitComputationCell(configInfo, labelInfo),
                "concretizing configuration");
        Function1<Module, Module> resolveFreshConstants = d -> ModuleTransformer.from(new ResolveFreshConstants(def, true)::resolve, "resolving !Var variables").apply(d);
        ModuleTransformer concretizeCells = ModuleTransformer.fromSentenceTransformer(
                new ConcretizeCells(configInfo, labelInfo, sortInfo, mod)::concretize,
                "concretizing configuration");

        return m -> resolveAnonVars
                .andThen(resolveSemanticCasts)
                .andThen(addImplicitComputationCell)
                .andThen(resolveFreshConstants)
                .andThen(concretizeCells)
                .andThen(subsortKItem)
                .apply(m);
    }

    @Override
    public Set<String> excludedModuleTags() {
        return Collections.singleton("symbolic");
    }
}
