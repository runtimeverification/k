package org.kframework.keq;

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
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.DefinitionLoadingModule;
import org.kframework.utils.inject.DefinitionScope;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Spec1;
import org.kframework.utils.inject.Spec2;

import java.io.File;
import java.util.List;
import java.util.function.Function;

public class KEqFrontEnd extends FrontEnd {
    private final DefinitionScope scope;
    private final Provider<File> kompiledDir;
    private final Provider<File> kompiledDir1;
    private final Provider<File> kompiledDir2;
    private final KExceptionManager kem;
    private final KEqOptions keqOptions;
    private final Provider<FileUtil> files;
    private final Stopwatch sw;
    private final Provider<Backend> backend;
    private final Provider<CompiledDefinition> compiledDef;
    private final Provider<CompiledDefinition> compiledDef1;
    private final Provider<CompiledDefinition> compiledDef2;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter1;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter2;

    @Inject
    public KEqFrontEnd(
            GlobalOptions globalOptions,
            @JCommanderModule.Usage String usage,
            @JCommanderModule.ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo,
            DefinitionScope scope,
            @Main(KompiledDir.class) Provider<File> kompiledDir,
            @Spec1(KompiledDir.class) Provider<File> kompiledDir1,
            @Spec2(KompiledDir.class) Provider<File> kompiledDir2,
            KExceptionManager kem,
            KEqOptions keqOptions,
            @Main Provider<FileUtil> files,
            Stopwatch sw,
            @Main Provider<Backend> backend,
            @Main Provider<CompiledDefinition> compiledDef,
            @Spec1 Provider<CompiledDefinition> compiledDef1,
            @Spec2 Provider<CompiledDefinition> compiledDef2,
            @Main Provider<Function<Definition, Rewriter>> initializeRewriter,
            @Spec1 Provider<Function<Definition, Rewriter>> initializeRewriter1,
            @Spec2 Provider<Function<Definition, Rewriter>> initializeRewriter2) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo, files);
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kompiledDir1 = kompiledDir1;
        this.kompiledDir2 = kompiledDir2;
        this.kem = kem;
        this.keqOptions = keqOptions;
        this.files = files;
        this.sw = sw;
        this.backend = backend;
        this.compiledDef = compiledDef;
        this.compiledDef1 = compiledDef1;
        this.compiledDef2 = compiledDef2;
        this.initializeRewriter = initializeRewriter;
        this.initializeRewriter1 = initializeRewriter1;
        this.initializeRewriter2 = initializeRewriter2;
    }

    @Override
    protected int run() {
        CompiledDefinition commonDef, def1, def2;
        Function<Definition, Rewriter> commonRewriter, rewriter1, rewriter2;
        Backend backend;
        scope.enter(kompiledDir.get());
        try {
            commonDef = compiledDef.get();
            commonRewriter = initializeRewriter.get();
            backend = this.backend.get();
        } finally {
            scope.exit();
        }
        scope.enter(kompiledDir1.get());
        try {
            def1 = compiledDef1.get();
            rewriter1 = initializeRewriter1.get();
        } finally {
            scope.exit();
        }
        scope.enter(kompiledDir2.get());
        try {
            def2 = compiledDef2.get();
            rewriter2 = initializeRewriter2.get();
        } finally {
            scope.exit();
        }
        return new KEq(kem, files.get(), sw).run(commonDef, def1, def2,
                keqOptions,
                backend,
                commonRewriter, rewriter1, rewriter2);
    }

    public static List<Module> getDefinitionSpecificModules() {
        return ImmutableList.of(
                new KEqModule.CommonModule(),
                new DefinitionLoadingModule());
    }

    public static List<Module> getModules(List<Module> definitionSpecificModules) {
        return ImmutableList.of(
                new KEqModule(),
                new CommonModule(),
                new JCommanderModule(),
                new KEqModule.MainExecutionContextModule(definitionSpecificModules),
                new KEqModule.Spec1ExecutionContextModule(definitionSpecificModules),
                new KEqModule.Spec2ExecutionContextModule(definitionSpecificModules));
    }
}
