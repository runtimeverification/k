// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.backend.html.HtmlBackend;
import org.kframework.backend.java.symbolic.JavaSymbolicBackend;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.backend.latex.LatexBackend;
import org.kframework.backend.latex.PdfBackend;
import org.kframework.backend.maude.KompileBackend;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.backend.unparser.UnflattenBackend;
import org.kframework.backend.unparser.UnparserBackend;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.CountNodesVisitor;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.options.SortedParameterDescriptions;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;

public class KompileFrontEnd {

    public static void main(String[] args) {
        KompileOptions options = new KompileOptions();
        options.global.initialize();
        try {
            JCommander jc = new JCommander(options, args);
            jc.setProgramName("kompile");
            jc.setParameterDescriptionComparator(new SortedParameterDescriptions(KompileOptions.Experimental.class));

            if (options.global.help) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0]);
                return;
            }

            if (options.helpExperimental) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString(), jc)[1]);
                return;
            }

            if (options.global.version) {
                String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.print(msg);
                return;
            }

            kompile(options);
        } catch (ParameterException ex) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, ex.getMessage()));
        }
    }

    private static void kompile(KompileOptions options) {
        org.kframework.utils.Error.checkIfOutputDirectory(options.directory);

        final Context context = new Context(options);

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

        Backend backend = null;
        switch (options.backend) {
            case PDF:
                backend = new PdfBackend(Stopwatch.instance(), context);
                break;
            case LATEX:
                backend = new LatexBackend(Stopwatch.instance(), context);
                break;
            case DOC:
                backend = new LatexBackend(Stopwatch.instance(), context, true);
                break;
            case HTML:
                backend = new HtmlBackend(Stopwatch.instance(), context);
                break;
            case KORE:
                backend = new KoreBackend(Stopwatch.instance(), context);
                return;
            case MAUDE:
                backend = new KompileBackend(Stopwatch.instance(), context);
                context.kompiled = new File(options.directory, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
                checkAnotherKompiled(context.kompiled);
                context.kompiled.mkdirs();
                break;
            case JAVA:
                backend = new JavaSymbolicBackend(Stopwatch.instance(), context);
                context.kompiled = new File(options.directory, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
                checkAnotherKompiled(context.kompiled);
                context.kompiled.mkdirs();
                break;
            case UNPARSE:
                backend = new UnparserBackend(Stopwatch.instance(), context);
                break;
            case UNFLATTEN:
                backend = new UnparserBackend(Stopwatch.instance(), context, true);
                break;
            case UNFLATTEN_JAVA:
                // TODO(YilongL): make it general to all backends; add info about
                // this backend in KompileOptionsParser
                Backend innerBackend = new JavaSymbolicBackend(Stopwatch.instance(), context);
                context.kompiled = new File(options.directory, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
                checkAnotherKompiled(context.kompiled);
                context.kompiled.mkdirs();
                backend = new UnflattenBackend(Stopwatch.instance(), context, innerBackend);
                break;
            case SYMBOLIC:
                backend = new SymbolicBackend(Stopwatch.instance(), context);
                context.kompiled = new File(options.directory, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
                checkAnotherKompiled(context.kompiled);
                context.kompiled.mkdirs();
                break;
            default:
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "Invalid backend option: " + backend, "", ""));
                break;
        }

        if (backend != null) {
            genericCompile(options, backend, options.experimental.step, context);
        }

        BinaryLoader.saveOrDie(new File(context.kompiled, "context.bin").getAbsolutePath(), context);

        verbose(context);
    }

    private static void verbose(Context context) {
        Stopwatch.instance().printTotal("Total");
        if (context.globalOptions.verbose) {
            context.printStatistics();
        }
    }


    private static void genericCompile(KompileOptions options, Backend backend, String step,
                                       Context context) {
        org.kframework.kil.Definition javaDef;
        Stopwatch.instance().start();
        javaDef = DefinitionLoader.loadDefinition(options.mainDefinitionFile(), options.mainModule(),
                backend.autoinclude(), context);

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

        BinaryLoader.saveOrDie(context.kompiled.getAbsolutePath() + "/configuration.bin",
                MetaK.getConfiguration(javaDef, context));

        backend.run(javaDef);

    }

    private static void checkAnotherKompiled(File kompiled) {
        File[] kompiledList = kompiled.getParentFile().listFiles(new FilenameFilter() {
            @Override
            public boolean accept(File current, String name) {
                File f = new File(current, name);
                return f.isDirectory() && f.getAbsolutePath().endsWith("-kompiled");
            }
        });
        for (File aKompiledList : kompiledList) {
            if (!aKompiledList.getName().equals(kompiled.getName())) {
                String msg = "Creating multiple kompiled definition in the same directory " +
                        "is not allowed.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, msg, "command line",
                        aKompiledList.getAbsolutePath()));
            }
        }
    }
}

