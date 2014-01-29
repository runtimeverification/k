package org.kframework.kompile;

import org.apache.commons.cli.CommandLine;
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
import org.kframework.krun.Main;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.OptionComparator;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class KompileFrontEnd {

    private static final String USAGE = "kompile [options] <file>" +
            System.getProperty("line.separator");
    private static final String HEADER_STANDARD = "";
    private static final String FOOTER_STANDARD = "";
    private static final String HEADER_EXPERIMENTAL = "Experimental options:";
    private static final String FOOTER_EXPERIMENTAL = Main.FOOTER_EXPERIMENTAL;

    public static void main(String[] args) throws IOException {
        KompileOptionsParser op = new KompileOptionsParser();
        CommandLine cmd = op.parse(args);

        if (cmd.hasOption("help"))
            printUsageS(op);
        else if (cmd.hasOption("help-experimental"))
            printUsageE(op);
        else if (cmd.hasOption("version")) {
            String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
            System.out.println(msg);
        } else if (cmd.getArgs().length < 1)
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                            "You have to provide a file in order to compile.",
                            "command line", "System file."));
        else {
            GlobalSettings.NOSMT |= "none".equals(cmd.getOptionValue("smt"));
            GlobalSettings.verbose |= cmd.hasOption("verbose");
            GlobalSettings.fastKast |= cmd.hasOption("fast-kast");
            GlobalSettings.warnings = cmd.getOptionValue("warnings", GlobalSettings.warnings);
            GlobalSettings.addTopCell |= cmd.hasOption("add-top-cell");
            GlobalSettings.lib = cmd.getOptionValue("lib", GlobalSettings.lib);
            GlobalSettings.synModule =
                    cmd.getOptionValue("syntax-module", GlobalSettings.synModule);
            GlobalSettings.testgen |= cmd.hasOption("test-gen");

            if (cmd.hasOption("transition"))
                GlobalSettings.transition = metadataParse(cmd.getOptionValue("transition"));
            if (cmd.hasOption("supercool"))
                GlobalSettings.supercool = metadataParse(cmd.getOptionValue("supercool"));
            if (cmd.hasOption("superheat"))
                GlobalSettings.superheat = metadataParse(cmd.getOptionValue("superheat"));
            if (cmd.hasOption("documentation"))
                GlobalSettings.doctags = metadataParse(cmd.getOptionValue("documentation"));
            
            if (cmd.hasOption("doc-style")) {
                String style = cmd.getOptionValue("doc-style");
                if (style.startsWith("+"))
                    GlobalSettings.style += style.replace("+", ",");
                else
                    GlobalSettings.style = style;
            }
            kompile(cmd);
        }
    }

    private static void kompile(CommandLine cmd) throws IOException {
        final String def = cmd.getArgs()[0];
        final String step = cmd.getOptionValue("step", null);
        GlobalSettings.setMainFile(def);
        GlobalSettings.outputDir = cmd.getOptionValue("directory",
                GlobalSettings.mainFile.getAbsoluteFile().getParent());
        org.kframework.utils.Error.checkIfOutputDirectory(GlobalSettings.outputDir);

        Context context = new Context();
        if (cmd.hasOption("kcells")) {
            String kCells = cmd.getOptionValue("kcells");
            List<String> komputationCells = new ArrayList<String>();
            Collections.addAll(komputationCells, kCells.split(" "));
            context.setKomputationCells(komputationCells);
            assert !context.getKomputationCells().isEmpty();
        }

        context.dotk = new File(GlobalSettings.outputDir + File.separator + ".k");
        context.dotk.mkdirs();

        Backend backend = null;
        String backendOpt = cmd.getOptionValue("backend", "maude");
        switch (backendOpt) {
            case "pdf":
                GlobalSettings.documentation = true;
                backend = new PdfBackend(Stopwatch.sw, context);
                break;
            case "latex":
                GlobalSettings.documentation = true;
                backend = new LatexBackend(Stopwatch.sw, context);
                break;
            case "doc":
                GlobalSettings.documentation = true;
                backend = new LatexBackend(Stopwatch.sw, context, true);                
            	break;
            case "html":
                if (!cmd.hasOption("doc-style")) {
                    GlobalSettings.style = "k-definition.css";
                }
                GlobalSettings.documentation = true;
                backend = new HtmlBackend(Stopwatch.sw, context);
                break;
            case "kore":
                backend = new KoreBackend(Stopwatch.sw, context);
                break;
            case "maude":
                backend = new KompileBackend(Stopwatch.sw, context);
                context.dotk = new File(GlobalSettings.outputDir + File.separator +
                        FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                break;
            case "java":
                GlobalSettings.javaBackend = true;
                backend = new JavaSymbolicBackend(Stopwatch.sw, context);
                context.dotk = new File(GlobalSettings.outputDir + File.separator +
                        FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                break;
            case "unparse":
                backend = new UnparserBackend(Stopwatch.sw, context);
                break;
            case "unflatten":
                backend = new UnparserBackend(Stopwatch.sw, context, true);
                break;
            case "unflatten-java":
                // TODO(YilongL): make it general to all backends; add info about
                // this backend in KompileOptionsParser
                GlobalSettings.javaBackend = true;
                Backend innerBackend = new JavaSymbolicBackend(Stopwatch.sw, context);
                context.dotk = new File(GlobalSettings.outputDir + File.separator +
                        FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                backend = new UnflattenBackend(Stopwatch.sw, context, innerBackend);
                break;
            case "symbolic":
                GlobalSettings.symbolic = true;
                backend = new SymbolicBackend(Stopwatch.sw, context);
                context.dotk = new File(GlobalSettings.outputDir + File.separator +
                        FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled");
                checkAnotherKompiled(context.dotk);
                context.dotk.mkdirs();
                if (cmd.hasOption("symbolic-rules")) {
                    GlobalSettings.symbolicTags = Arrays.asList(
                            cmd.getOptionValue("symbolic-rules").trim().split("\\s+"));
                }
                if (cmd.hasOption("non-symbolic-rules")) {
                    GlobalSettings.nonSymbolicTags = Arrays.asList(
                            cmd.getOptionValue("non-symbolic-rules").trim().split("\\s+"));
                }
                break;
            default:
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "Invalid backend option: " + backendOpt, "", ""));
                break;
        }

        if (backend != null) {
            String lang = cmd.getOptionValue("main-module",
                    FileUtil.getMainModule(GlobalSettings.mainFile.getName()));
            genericCompile(lang, backend, step, context);
        }

        verbose(cmd, context);
    }

    private static void verbose(CommandLine cmd, Context context) {
        Stopwatch.sw.printTotal("Total");
        if (GlobalSettings.verbose) {
            context.printStatistics();
        }
        GlobalSettings.kem.print();
        if (cmd.hasOption("loud"))
            System.out.println("Done.");
    }


    private static void genericCompile(String lang, Backend backend, String step,
                                       Context context) throws IOException {
        org.kframework.kil.Definition javaDef;
        Stopwatch.sw.start();
        javaDef = DefinitionLoader.loadDefinition(GlobalSettings.mainFile, lang,
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

    private static void printUsageS(KompileOptionsParser op) {
        org.kframework.utils.Error.helpMsg(USAGE, HEADER_STANDARD, FOOTER_STANDARD,
                op.getOptionsStandard(), new OptionComparator(op.getOptionList()));
    }

    private static void printUsageE(KompileOptionsParser op) {
        org.kframework.utils.Error.helpMsg(USAGE, HEADER_EXPERIMENTAL, FOOTER_EXPERIMENTAL,
                op.getOptionsExperimental(), new OptionComparator(op.getOptionList()));
    }

    private static List<String> metadataParse(String tags) {
        String[] alltags = tags.split("\\s+");
        List<String> result = new ArrayList<String>();
        Collections.addAll(result, alltags);
        return result;
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

