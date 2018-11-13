// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.Strategy;
import org.kframework.compile.AddImplicitComputationCell;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.Backend;
import org.kframework.compile.ConcretizeCells;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.GenerateSortPredicateRules;
import org.kframework.compile.GenerateSortPredicateSyntax;
import org.kframework.compile.MinimizeTermConstruction;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.compile.ResolveContexts;
import org.kframework.compile.ResolveFreshConstants;
import org.kframework.compile.ResolveFun;
import org.kframework.compile.ResolveHeatCoolAttribute;
import org.kframework.compile.ResolveSemanticCasts;
import org.kframework.compile.ResolveStrict;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
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
        Module mainModule = def.kompiledDefinition.mainModule();
        mainModule = new GenerateSortPredicateRules(true).gen(mainModule);
        mainModule = ModuleTransformer.fromKTransformer(new AddSortInjections(mainModule)::addInjections, "Add sort injections").apply(mainModule);
        mainModule = ModuleTransformer.fromSentenceTransformer(new MinimizeTermConstruction(mainModule)::resolve, "Minimize term construction").apply(mainModule);
        ModuleToKORE moduleToKORE = new ModuleToKORE(mainModule, files, def.topCellInitializer);
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
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(true)::resolve, "resolving semantic casts");
        DefinitionTransformer resolveFun = DefinitionTransformer.from(new ResolveFun()::resolve, "resolving #fun");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");
        DefinitionTransformer subsortKItem = DefinitionTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
        DefinitionTransformer expandMacros = DefinitionTransformer.fromSentenceTransformer((m, s) -> new ExpandMacros(m, files, kompileOptions, false).expand(s), "expand macros");
        Function1<Definition, Definition> resolveFreshConstants = d -> DefinitionTransformer.from(new ResolveFreshConstants(d, true)::resolve, "resolving !Var variables").apply(d);
        Function1<Definition, Definition> resolveIO = (d -> Kompile.resolveIOStreams(kem, d));

        return def -> resolveIO
                .andThen(resolveFun)
                .andThen(resolveStrict)
                .andThen(expandMacros)
                .andThen(resolveAnonVars)
                .andThen(d -> new ResolveContexts(kompileOptions).resolve(d))
                .andThen(resolveHeatCoolAttribute)
                .andThen(resolveSemanticCasts)
                .andThen(generateSortPredicateSyntax)
                .andThen(AddImplicitComputationCell::transformDefinition)
                .andThen(resolveFreshConstants)
                .andThen(new Strategy(kompileOptions.experimental.heatCoolStrategies).addStrategyCellToRulesTransformer())
                .andThen(d -> Strategy.addStrategyRuleToMainModule(def.mainModule().name()).apply(d))
                .andThen(ConcretizeCells::transformDefinition)
                .andThen(subsortKItem)
                .andThen(Kompile::addSemanticsModule)
                .apply(def);
    }

    @Override
    public Function<Module, Module> specificationSteps(Definition def) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<String> excludedModuleTags() {
        return Collections.singleton("symbolic");
    }
}
