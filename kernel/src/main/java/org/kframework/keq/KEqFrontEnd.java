package org.kframework.keq;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;
import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kprove.ProofDefinitionBuilder;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
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
    private final Provider<FileUtil> files;
    private final Provider<CompiledDefinition> compiledDef;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter1;
    private final Provider<Function<Definition, Rewriter>> initializeRewriter2;
    private final Provider<ProofDefinitionBuilder> pdb1Provider;
    private final Provider<ProofDefinitionBuilder> pdb2Provider;
    private final Provider<KEq> keq;

    @Inject
    public KEqFrontEnd(
            GlobalOptions globalOptions,
            @JCommanderModule.Usage String usage,
            JarInfo jarInfo,
            DefinitionScope scope,
            @Main(KompiledDir.class) Provider<File> kompiledDir,
            @Spec1(KompiledDir.class) Provider<File> kompiledDir1,
            @Spec2(KompiledDir.class) Provider<File> kompiledDir2,
            KExceptionManager kem,
            @Main Provider<FileUtil> files,
            @Main Provider<CompiledDefinition> compiledDef,
            @Main Provider<Function<Definition, Rewriter>> initializeRewriter,
            @Spec1 Provider<Function<Definition, Rewriter>> initializeRewriter1,
            @Spec2 Provider<Function<Definition, Rewriter>> initializeRewriter2,
            @Spec1 Provider<ProofDefinitionBuilder> pdb1Provider,
            @Spec2 Provider<ProofDefinitionBuilder> pdb2Provider,
            Provider<KEq> keq) {
        super(kem, globalOptions, usage, jarInfo, files);
        this.scope = scope;
        this.kompiledDir = kompiledDir;
        this.kompiledDir1 = kompiledDir1;
        this.kompiledDir2 = kompiledDir2;
        this.files = files;
        this.compiledDef = compiledDef;
        this.initializeRewriter = initializeRewriter;
        this.initializeRewriter1 = initializeRewriter1;
        this.initializeRewriter2 = initializeRewriter2;
        this.pdb1Provider = pdb1Provider;
        this.pdb2Provider = pdb2Provider;
        this.keq = keq;
    }

    @Override
    protected int run() {
        CompiledDefinition commonDef;
        ProofDefinitionBuilder pdb1, pdb2;
        Function<Definition, Rewriter> commonGen, gen1, gen2;
        scope.enter(kompiledDir.get());
        try {
            commonDef = compiledDef.get();
            commonGen = initializeRewriter.get();
        } finally {
            scope.exit();
        }
        scope.enter(kompiledDir1.get());
        try {
            pdb1 = pdb1Provider.get();
            gen1 = initializeRewriter1.get();
        } finally {
            scope.exit();
        }
        scope.enter(kompiledDir2.get());
        try {
            pdb2 = pdb2Provider.get();
            gen2 = initializeRewriter2.get();
        } finally {
            scope.exit();
        }
        return keq.get().run(commonDef, commonGen, gen1, gen2, pdb1, pdb2, files.get());
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
