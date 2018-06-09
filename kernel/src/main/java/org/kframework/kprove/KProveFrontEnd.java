// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.kprove;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.compile.Backend;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunModule;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.RewriterModule;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;

import java.io.File;
import java.util.List;
import java.util.function.Function;

public class KProveFrontEnd extends FrontEnd {


    public static List<Module> getModules() {
        return ImmutableList.<Module>of(
                new KProveModule(),
                new CommonModule(),
                new JCommanderModule(),
                new DefinitionLoadingModule());
    }


    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final KExceptionManager kem;
    private final KProveOptions kproveOptions;
    private final FileUtil files;
    private final Provider<CompiledDefinition> compiledDef;
    private final Provider<Backend> backend;
    private final Provider<Function<org.kframework.definition.Module, Rewriter>> initializeRewriter;
    private final TTYInfo tty;
    private final Stopwatch sw;

    @Inject
    KProveFrontEnd(
            GlobalOptions options,
            @JCommanderModule.Usage String usage,
            @JCommanderModule.ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            DefinitionScope scope,
            @KompiledDir Provider<File> kompiledDir,
            KExceptionManager kem,
            KProveOptions kproveOptions,
            FileUtil files,
            Provider<CompiledDefinition> compiledDef,
            Provider<Backend> backend,
            Provider<Function<org.kframework.definition.Module, Rewriter>> initializeRewriter,
            TTYInfo tty,
            Stopwatch sw) {
        super(kem, options, usage, experimentalUsage, jarInfo, files);
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kem = kem;
        this.kproveOptions = kproveOptions;
        this.files = files;
        this.compiledDef = compiledDef;
        this.backend = backend;
        this.initializeRewriter = initializeRewriter;
        this.tty = tty;
        this.sw = sw;
    }

    @Override
    protected int run() {
        scope.enter(kompiledDir.get());
        try {
            if (!kproveOptions.specFile(files).exists()) {
                throw KEMException.criticalError("Definition file doesn't exist: " +
                        kproveOptions.specFile(files).getAbsolutePath());
            }
            return new KProve(kem, sw, files, tty).run(kproveOptions, compiledDef.get(), backend.get(), initializeRewriter.get());
        } finally {
            scope.exit();
        }
    }
}
