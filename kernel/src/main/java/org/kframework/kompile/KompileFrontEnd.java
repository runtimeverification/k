// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.Backend;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.CountNodesVisitor;
import org.kframework.main.FrontEnd;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.CommonModule;

import com.google.inject.Inject;
import com.google.inject.Module;

public class KompileFrontEnd extends FrontEnd {

    public static List<Module> getModules(String[] args) {
        KompileOptions options = new KompileOptions();

        final Context context = new Context();
        context.kompileOptions = options;

        List<Module> modules = new ArrayList<>();
        modules.add(new KompileModule(context, options));
        modules.add(new JCommanderModule(args));
        modules.add(new CommonModule());
        return modules;
    }


    private final Context context;
    private final KompileOptions options;
    private final Backend backend;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final DefinitionLoader defLoader;
    private final FileUtil files;

    @Inject
    KompileFrontEnd(
            Context context,
            KompileOptions options,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Backend backend,
            Stopwatch sw,
            KExceptionManager kem,
            BinaryLoader loader,
            DefinitionLoader defLoader,
            JarInfo jarInfo,
            FileUtil files) {
        super(kem, options.global, usage, experimentalUsage, jarInfo, files);
        this.context = context;
        this.options = options;
        this.backend = backend;
        this.sw = sw;
        this.kem = kem;
        this.loader = loader;
        this.defLoader = defLoader;
        this.files = files;
    }

    @Override
    public boolean run() {
        if (!options.mainDefinitionFile().exists()) {
            throw KExceptionManager.criticalError("Definition file doesn't exist: " +
                    options.mainDefinitionFile().getAbsolutePath());
        }

        context.files = files;

        Definition def = genericCompile(options.experimental.step);

        loader.saveOrDie(files.resolveKompiled("context.bin"), context);
        loader.saveOrDie(files.resolveKompiled("definition.bin"), def);

        verbose(def);
        return true;
    }

    private void verbose(Definition def) {
        sw.printTotal("Total");
        if (context.globalOptions.verbose) {
            CountNodesVisitor visitor = new CountNodesVisitor();
            visitor.visitNode(def);
            visitor.printStatistics();
        }
    }

    private Definition genericCompile(String step) {
        org.kframework.kil.Definition javaDef;
        sw.start();
        javaDef = defLoader.loadDefinition(options.mainDefinitionFile(), options.mainModule(),
                context);

        loader.saveOrDie(files.resolveKompiled("definition-concrete.bin"), javaDef);

        CompilerSteps<Definition> steps = backend.getCompilationSteps();

        if (step == null) {
            step = backend.getDefaultStep();
        }
        try {
            javaDef = steps.compile(javaDef, step);
        } catch (CompilerStepDone e) {
            javaDef = (Definition) e.getResult();
        }

        loader.saveOrDie(files.resolveKompiled("configuration.bin"),
                MetaK.getConfiguration(javaDef, context));

        backend.run(javaDef);

        return javaDef;
    }
}

