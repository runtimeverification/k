// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import com.google.inject.Inject;
import org.apache.commons.io.FilenameUtils;
import org.kframework.Strategy;
import org.kframework.backend.Backends;
import org.kframework.compile.AddImplicitComputationCell;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.Backend;
import org.kframework.compile.ConcretizeCells;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.GenerateCoverage;
import org.kframework.compile.GenerateSortPredicateRules;
import org.kframework.compile.GenerateSortPredicateSyntax;
import org.kframework.compile.NumberSentences;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.compile.ResolveContexts;
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
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;

import java.io.File;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

public class KoreBackend implements Backend {

    private final KompileOptions kompileOptions;
    private final FileUtil files;
    private final KExceptionManager kem;

    @Inject
    public KoreBackend(
            KompileOptions kompileOptions,
            FileUtil files,
            KExceptionManager kem) {
        this.kompileOptions = kompileOptions;
        this.files = files;
        this.kem = kem;
    }


    @Override
    public void accept(CompiledDefinition def) {
        Module mainModule = def.kompiledDefinition.mainModule();
        mainModule = new GenerateSortPredicateRules(true).gen(mainModule);
        mainModule = ModuleTransformer.fromKTransformer(new AddSortInjections(mainModule)::addInjections, "Add sort injections").apply(mainModule);
        String kore = new ModuleToKORE(mainModule, files).convert();
        File defFile = kompileOptions.outerParsing.mainDefinitionFile(files);
        String name = defFile.getName();
        String basename = FilenameUtils.removeExtension(name);
        files.saveToDefinitionDirectory(basename + ".kore", kore);
    }

    @Override
    public Function<Definition, Definition> steps() {
        DefinitionTransformer resolveStrict = DefinitionTransformer.from(new ResolveStrict(kompileOptions)::resolve, "resolving strict and seqstrict attributes");
        DefinitionTransformer resolveAnonVars = DefinitionTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolving \"_\" vars");
        DefinitionTransformer resolveSemanticCasts =
                DefinitionTransformer.fromSentenceTransformer(new ResolveSemanticCasts(true)::resolve, "resolving semantic casts");
        DefinitionTransformer resolveFun = DefinitionTransformer.from(new ResolveFun()::resolve, "resolving #fun");
        DefinitionTransformer generateSortPredicateSyntax = DefinitionTransformer.from(new GenerateSortPredicateSyntax()::gen, "adding sort predicate productions");
        DefinitionTransformer subsortKItem = DefinitionTransformer.from(Kompile::subsortKItem, "subsort all sorts to KItem");
        DefinitionTransformer expandMacros = DefinitionTransformer.fromSentenceTransformer((m, s) -> new ExpandMacros(m, files, kompileOptions, false).expand(s), "expand macros");

        return def -> Kompile.excludeModulesByTag(excludedModuleTags(), def)
                .andThen(d -> Kompile.resolveIOStreams(kem, d))
                .andThen(resolveFun)
                .andThen(resolveStrict)
                .andThen(expandMacros)
                .andThen(resolveAnonVars)
                .andThen(d -> new ResolveContexts(kompileOptions).resolve(d))
                .andThen(resolveSemanticCasts)
                .andThen(generateSortPredicateSyntax)
                .andThen(AddImplicitComputationCell::transformDefinition)
                .andThen(new Strategy(kompileOptions.experimental.heatCoolStrategies).addStrategyCellToRulesTransformer())
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
