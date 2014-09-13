// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.backend.java.symbolic.JavaSymbolicCommonModule;
import org.kframework.backend.java.symbolic.JavaSymbolicKompileModule;
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
import com.beust.jcommander.ParameterException;
import com.google.inject.Inject;
import com.google.inject.Module;

public class KompileFrontEnd extends FrontEnd {

    public static Module[] getModules(String[] args) {
        try {
            KompileOptions options = new KompileOptions();

            final Context context = new Context();
            context.kompileOptions = options;

            return new Module[] {
                    new KompileModule(context, options),
                    new JCommanderModule(args),
                    new CommonModule(),
                    new JavaSymbolicCommonModule(),
                    new JavaSymbolicKompileModule() };
        } catch (ParameterException ex) {
            printBootError(ex.getMessage());
            return null;
        }
    }


    private final Context context;
    private final KompileOptions options;
    private final Backend backend;
    private final Stopwatch sw;
    private final KExceptionManager kem;
    private final BinaryLoader loader;
    private final DefinitionLoader defLoader;

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
            JarInfo jarInfo) {
        super(kem, options.global, usage, experimentalUsage, jarInfo);
        this.context = context;
        this.options = options;
        this.backend = backend;
        this.sw = sw;
        this.kem = kem;
        this.loader = loader;
        this.defLoader = defLoader;
    }

    @Override
    public boolean run() {
        if (options.directory.isFile()) { // isFile = exists && !isDirectory
            String msg = "Not a directory: " + options.directory;
            kem.registerCriticalError(msg);
        }

        context.dotk = new File(options.directory, ".k/" + FileUtil.generateUniqueFolderName("kompile"));
        context.dotk.mkdirs();

        // default for documentation backends is to store intermediate outputs in temp directory
        context.kompiled = context.dotk;

        if (!options.global.debug) {
            Runtime.getRuntime().addShutdownHook(new Thread() {
                public void run() {
                    try {
                        FileUtils.deleteDirectory(context.dotk);
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            });
        }

        if (backend.generatesDefinition()) {
                context.kompiled = new File(options.directory, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
                checkAnotherKompiled(context.kompiled);
                context.kompiled.mkdirs();
        }

        genericCompile(options.experimental.step);

        loader.saveOrDie(new File(context.kompiled, "context.bin").getAbsolutePath(), context);

        verbose();
        return true;
    }

    private void verbose() {
        sw.printTotal("Total");
        if (context.globalOptions.verbose) {
            context.printStatistics();
        }
    }


    private void genericCompile(String step) {
        org.kframework.kil.Definition javaDef;
        sw.start();
        javaDef = defLoader.loadDefinition(options.mainDefinitionFile(), options.mainModule(),
                context);

        new CountNodesVisitor(context).visitNode(javaDef);

        CompilerSteps<Definition> steps = backend.getCompilationSteps();

        if (step == null) {
            step = backend.getDefaultStep();
        }
        try {
            javaDef = steps.compile(javaDef, step);
        } catch (CompilerStepDone e) {
            javaDef = (Definition) e.getResult();
        }

        loader.saveOrDie(context.kompiled.getAbsolutePath() + "/configuration.bin",
                MetaK.getConfiguration(javaDef, context));

        backend.run(javaDef);

    }

    private void checkAnotherKompiled(File kompiled) {
        File[] kompiledList = kompiled.getParentFile().listFiles(new FilenameFilter() {
            @Override
            public boolean accept(File current, String name) {
                File f = new File(current, name);
                return f.getAbsolutePath().endsWith("-kompiled") && f.isDirectory();
            }
        });
        for (File aKompiledList : kompiledList) {
            if (!aKompiledList.getName().equals(kompiled.getName())) {
                String msg = "Creating multiple kompiled definition in the same directory " +
                        "is not allowed. Found " + aKompiledList.getName() + " and " + kompiled.getName() + ".";
                kem.registerCriticalError(msg);
            }
        }
    }
}

