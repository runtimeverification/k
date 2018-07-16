// Copyright (c) 2012-2018 K Team. All Rights Reserved.
package org.kframework.krun;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.io.File;
import java.util.List;
import java.util.function.Function;

public class KRunFrontEnd extends FrontEnd {

    public static List<Module> getModules() {
        return ImmutableList.<Module>of(
                new KRunModule(),
                new CommonModule(),
                new JCommanderModule(),
                new KRunModule.CommonModule(),
                new DefinitionLoadingModule());
    }


    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final KExceptionManager kem;
    private final KRunOptions krunOptions;
    private final FileUtil files;
    private final Provider<CompiledDefinition> compiledDef;
    private final Provider<Function<org.kframework.definition.Module, Rewriter>> initializeRewriter;
    private final Provider<ExecutionMode> executionMode;
    private final TTYInfo tty;

    @Inject
    KRunFrontEnd(
            GlobalOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            DefinitionScope scope,
            @KompiledDir Provider<File> kompiledDir,
            KExceptionManager kem,
            KRunOptions krunOptions,
            FileUtil files,
            Provider<CompiledDefinition> compiledDef,
            Provider<Function<org.kframework.definition.Module, Rewriter>> initializeRewriter,
            Provider<ExecutionMode> executionMode,
            TTYInfo tty) {
        super(kem, options, usage, experimentalUsage, jarInfo, files);
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kem = kem;
        this.krunOptions = krunOptions;
        this.files = files;
        this.compiledDef = compiledDef;
        this.initializeRewriter = initializeRewriter;
        this.executionMode = executionMode;
        this.tty = tty;
    }

    /**
     * @return the exit code returned from executing krun.
     */
    public int run() {
        scope.enter(kompiledDir.get());
        try {
            KPrint kprint = new KPrint(kem, files, tty, krunOptions.print);
            for (int i = 0; i < krunOptions.experimental.profile - 1; i++) {
                new KRun(kem, files, tty, kprint).run(compiledDef.get(),
                        krunOptions,
                        initializeRewriter.get(),
                        executionMode.get());
            }
            return new KRun(kem, files, tty, kprint).run(compiledDef.get(),
                    krunOptions,
                    initializeRewriter.get(),
                    executionMode.get());
        } finally {
            scope.exit();
        }
    }
}
