package org.kframework.kompile;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;

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
import org.kframework.krun.K;
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

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;

public class KompileFrontEnd {

    public static void main(String[] args) throws IOException {
        KompileOptions options = new KompileOptions();
        options.global.initialize();
        try {
            JCommander jc = new JCommander(options, args);
            jc.setProgramName("kompile");
            
            if (options.help) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString())[0]);
                return;
            }
            
            if (options.helpExperimental) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString())[1]);
                return;    
            }
            
            if (options.version) {
                String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.print(msg);
                return;
            }
            
            kompile(options);
        } catch (ParameterException ex) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, ex.getMessage()));
        }
    }

    private static void kompile(KompileOptions options) throws IOException {
        K.do_kompilation = true;
        org.kframework.utils.Error.checkIfOutputDirectory(options.directory);

        Context context = new Context(options);
        
        context.dotk = new File(options.directory, ".k");
        context.dotk.mkdirs();

        Backend backend = null;
        switch (options.backend) {
            case pdf:
                backend = new PdfBackend(Stopwatch.instance(), context);
                break;
            case latex:
                backend = new LatexBackend(Stopwatch.instance(), context);
                break;
            case doc:
                backend = new LatexBackend(Stopwatch.instance(), context, true);                
                break;
            case html:
                backend = new HtmlBackend(Stopwatch.instance(), context);
                break;
            case kore:
                backend = new KoreBackend(Stopwatch.instance(), context);
                backend.run(DefinitionLoader.loadDefinition(options.definition(), options.mainModule(),
                        backend.autoinclude(), context));
                return;
            case maude:
                backend = new KompileBackend(Stopwatch.instance(), context);
                context.dotk = new File(options.directory, FilenameUtils.removeExtension(options.definition().getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                break;
            case java:
                backend = new JavaSymbolicBackend(Stopwatch.instance(), context);
                context.dotk = new File(options.directory, FilenameUtils.removeExtension(options.definition().getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                break;
            case unparse:
                backend = new UnparserBackend(Stopwatch.instance(), context);
                break;
            case unflatten:
                backend = new UnparserBackend(Stopwatch.instance(), context, true);
                break;
            case unflatten_java:
                // TODO(YilongL): make it general to all backends; add info about
                // this backend in KompileOptionsParser
                Backend innerBackend = new JavaSymbolicBackend(Stopwatch.instance(), context);
                context.dotk = new File(options.directory, FilenameUtils.removeExtension(options.definition().getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                backend = new UnflattenBackend(Stopwatch.instance(), context, innerBackend);
                break;
            case symbolic:
                backend = new SymbolicBackend(Stopwatch.instance(), context);
                context.dotk = new File(options.directory, FilenameUtils.removeExtension(options.definition().getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                break;
            default:
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "Invalid backend option: " + backend, "", ""));
                break;
        }

        if (backend != null) {
            genericCompile(options, backend, options.experimental.step, context);
        }
        
        BinaryLoader.save(new File(context.dotk, "kompile-options.bin").getAbsolutePath(), options);

        verbose(context);
    }

    private static void verbose(Context context) {
        Stopwatch.instance().printTotal("Total");
        if (context.globalOptions.verbose) {
            context.printStatistics();
        }
        GlobalSettings.kem.print();
        if (context.kompileOptions.experimental.loud)
            System.out.println("Done.");
    }


    private static void genericCompile(KompileOptions options, Backend backend, String step,
                                       Context context) throws IOException {
        org.kframework.kil.Definition javaDef;
        Stopwatch.instance().start();
        javaDef = DefinitionLoader.loadDefinition(options.definition(), options.mainModule(),
                backend.autoinclude(), context);
        
        javaDef.accept(new CountNodesVisitor(context));
        
        CompilerSteps<Definition> steps = backend.getCompilationSteps();

        if (step == null) {
            step = backend.getDefaultStep();
        }
        try {
            javaDef = steps.compile(javaDef, step);
        } catch (CompilerStepDone e) {
            javaDef = (Definition) e.getResult();
        }

        BinaryLoader.save(context.dotk.getAbsolutePath() + "/configuration.bin",
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

