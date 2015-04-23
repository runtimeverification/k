// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.kil.Attributes;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.tools.Executor;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.transformation.AmbiguousTransformationException;
import org.kframework.transformation.Transformation;
import org.kframework.transformation.TransformationNotSatisfiedException;
import org.kframework.transformation.TransformationProvider;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.Main;

import java.io.File;
import java.util.List;
import java.util.function.Function;

public class KRunFrontEnd extends FrontEnd {

    public static List<Module> getDefinitionSpecificModules() {
        return ImmutableList.<Module>of(
                new KRunModule.CommonModule(),
                new DefinitionLoadingModule()
        );
    }

    public static List<Module> getModules(List<Module> definitionSpecificModules) {
        return ImmutableList.<Module>of(
                new KRunModule(),
                new CommonModule(),
                new JCommanderModule(),
                new KRunModule.MainExecutionContextModule(definitionSpecificModules));
    }


    private final TransformationProvider<Transformation<Void, Void>> toolProvider;
    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final KRunOptions kRunOptions;
    private final Provider<NewKRunFrontEnd> newFrontEnd;

    @Inject
    KRunFrontEnd(
            GlobalOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            TransformationProvider<Transformation<Void, Void>> toolProvider,
            KExceptionManager kem,
            JarInfo jarInfo,
            @Main FileUtil files,
            DefinitionScope scope,
            @Main(KompiledDir.class) Provider<File> kompiledDir,
            KRunOptions kRunOptions,
            Provider<NewKRunFrontEnd> newFrontEnd) {
        super(kem, options, usage, experimentalUsage, jarInfo, files);
        this.toolProvider = toolProvider;
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kRunOptions = kRunOptions;
        this.newFrontEnd = newFrontEnd;
    }

    // TODO(dwightguth): inline when we remove kil
    public static class NewKRunFrontEnd {

        private final KExceptionManager kem;
        private final KRunOptions krunOptions;
        private final FileUtil files;
        private final CompiledDefinition compiledDef;
        private final Function<org.kframework.definition.Module, org.kframework.Rewriter> initializeRewriter;

        @Inject
        public NewKRunFrontEnd(KExceptionManager kem, KRunOptions krunOptions, @Main FileUtil files, @Main CompiledDefinition compiledDef, @Main Function<org.kframework.definition.Module, org.kframework.Rewriter> initializeRewriter) {
            this.kem = kem;
            this.krunOptions = krunOptions;
            this.files = files;
            this.compiledDef = compiledDef;
            this.initializeRewriter = initializeRewriter;
        }

        public int run() {
            return new KRun(kem, files).run(compiledDef,
                    krunOptions,
                    initializeRewriter);
        }
    }

    /**
     * @param cmds represents the arguments/options given to krun command..
     * @return true if the application completed normally; false otherwise
     */
    public int run() {
        try {
            scope.enter(kompiledDir.get());
            try {
                if (kRunOptions.experimental.kore) {
                    return newFrontEnd.get().run();
                } else {
                    Transformation<Void, Void> tool = toolProvider.get();
                    Attributes a = new Attributes();
                    tool.run(null, a);
                    Integer exitCode = a.typeSafeGet(Integer.class, Executor.Tool.EXIT_CODE);
                    if (exitCode == null) {
                        exitCode = 0;
                    }
                    return exitCode;
                }
            } finally {
                scope.exit();
            }
        } catch (TransformationNotSatisfiedException
                | AmbiguousTransformationException e) {
            throw KEMException.criticalError(e.getMessage(), e);
        }
    }
}
