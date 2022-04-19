// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.ksearchpattern;

import com.google.inject.Provider;
import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.Module;
import org.kframework.attributes.Source;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.builtin.BooleanUtils;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Frontend for k-compiled-search-pattern tool.
 * <p>
 * k-compile-search-patterrn is used by the new krun frontend in order to
 * convert a search pattern written as a rule bubble into a KORE search pattern
 * for the Haskell backend.
 */
public class KSearchPatternFrontEnd extends FrontEnd {

    private final KSearchPatternOptions options;
    private final Provider<KompileOptions> kompileOptions;
    private final KExceptionManager kem;
    private final Provider<FileUtil> files;
    private final GlobalOptions globalOptions;
    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final Provider<CompiledDefinition> compiledDef;

    @Inject
    public KSearchPatternFrontEnd(
            KSearchPatternOptions options,
            KExceptionManager kem,
            Provider<KompileOptions> kompileOptions,
            GlobalOptions globalOptions,
            @Usage String usage,
            JarInfo jarInfo,
            Provider<FileUtil> files,
            @KompiledDir Provider<File> kompiledDir,
            Provider<CompiledDefinition> compiledDef,
            DefinitionScope scope) {
        super(kem, globalOptions, usage, jarInfo, files);
        this.options = options;
        this.kompileOptions = kompileOptions;
        this.globalOptions = globalOptions;
        this.kem = kem;
        this.files = files;
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.compiledDef = compiledDef;
    }

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KSearchPatternModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    @Override
    protected int run() {
        scope.enter(kompiledDir.get());
        try {
          FileUtil files = this.files.get();
          CompiledDefinition compiledDef = this.compiledDef.get();
          KompileOptions kompileOptions = this.kompileOptions.get();
          Rule pattern = compiledDef.compilePatternIfAbsent(files, kem, options.pattern(), Source.apply("<command line>"));
          K patternTerm = RewriteToTop.toLeft(pattern.body());
          K patternCondition = pattern.requires();
          org.kframework.definition.Module mod = compiledDef.executionModule();
          AddSortInjections addSortInjections = new AddSortInjections(mod);
          ModuleToKORE converter = new ModuleToKORE(mod, compiledDef.topCellInitializer, kompileOptions);
          StringBuilder sb = new StringBuilder();
          ExpandMacros macroExpander = ExpandMacros.forNonSentences(mod, files, kompileOptions, false);
          K withMacros = macroExpander.expand(patternTerm);
          K kWithInjections = addSortInjections.addInjections(withMacros);
          sb.append("\\and{SortGeneratedTopCell{}}(");
          converter.convert(kWithInjections, sb);
          sb.append(", ");
          if (patternCondition.equals(BooleanUtils.TRUE)) {
            sb.append("\\top{SortGeneratedTopCell{}}()");
          } else {
            sb.append("\\equals{SortBool{},SortGeneratedTopCell{}}(");
            withMacros = macroExpander.expand(patternCondition);
            kWithInjections = addSortInjections.addInjections(withMacros);
            converter.convert(kWithInjections, sb);
            sb.append(", \\dv{SortBool{}}(\"true\"))");
          }
          sb.append(")");
          System.out.println(sb.toString());
          return 0;
        } finally {
            scope.exit();
        }
    }
}
