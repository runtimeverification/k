// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kbmc;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.KPrint;
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

public class KBMCFrontEnd extends FrontEnd {


    public static List<Module> getModules() {
        return ImmutableList.<Module>of(
                new KBMCModule(),
                new CommonModule(),
                new JCommanderModule(),
                new DefinitionLoadingModule());
    }


    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final KExceptionManager kem;
    private final KBMCOptions kbmcOptions;
    private final Provider<FileUtil> files;
    private final Provider<CompiledDefinition> compiledDef;
    private final Provider<Backend> backend;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter;
    private final TTYInfo tty;
    private final Stopwatch sw;

    @Inject
    public KBMCFrontEnd(
            GlobalOptions options,
            @JCommanderModule.Usage String usage,
            @JCommanderModule.ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            DefinitionScope scope,
            @KompiledDir Provider<File> kompiledDir,
            KExceptionManager kem,
            KBMCOptions kbmcOptions,
            Provider<FileUtil> files,
            Provider<CompiledDefinition> compiledDef,
            Provider<Backend> backend,
            Provider<Function<Definition, Rewriter>> initializeRewriter,
            TTYInfo tty,
            Stopwatch sw) {
        super(kem, options, usage, experimentalUsage, jarInfo, files);
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kem = kem;
        this.kbmcOptions = kbmcOptions;
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
            if (!kbmcOptions.specFile(files.get()).exists()) {
                throw KEMException.criticalError("Definition file doesn't exist: " +
                        kbmcOptions.specFile(files.get()).getAbsolutePath());
            }
            KPrint kprint = new KPrint(kem, files.get(), tty, kbmcOptions.print, compiledDef.get());
            return new KBMC(kem, sw, files.get(), kprint).run(kbmcOptions, compiledDef.get(), backend.get(),
                    initializeRewriter.get());
        } finally {
            scope.exit();
        }
    }
}
