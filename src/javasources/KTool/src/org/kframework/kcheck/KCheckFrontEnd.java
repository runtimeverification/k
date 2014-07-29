// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck;

import org.kframework.backend.Backend;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kcheck.gui.KCheckMainWindow;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.CountNodesVisitor;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class KCheckFrontEnd {
    public static String output;
    //public static CommandLine cmd;

    /**
     *
     * @param args
     * @return true if the application completed normally; false otherwise
     */
    public static boolean kcheck(String[] args) {
        KCheckOptionsParser op = new KCheckOptionsParser();

        //cmd = op.parse(args);

        // options: help
        //if (cmd.hasOption("help"))
            //org.kframework.utils.Error.helpExit(op.getHelp(), op.getOptions());

        //if (cmd.hasOption("version")) {
            String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
            System.out.println(msg);
            //return true;
        //}

        // main settings
        //GlobalSettings.symbolicEquality = true;
        //GlobalSettings.SMT = true;
        //GlobalSettings.NOSMT = false;
        //RLBackend.SIMPLIFY = cmd.hasOption("simplify");
        //GlobalSettings.addTopCell = true;


        // set verbose
        //if (cmd.hasOption("verbose"))
        //    GlobalSettings.verbose = true;


        // user interface
        //if (cmd.hasOption("interface")) {
            KCheckMainWindow kcheck = new KCheckMainWindow();
            kcheck.setVisible(true);
        //} else {

            //if (cmd.hasOption("pgm")) {
            //    RLBackend.PGM = cmd.getOptionValue("pgm");
            //}


            //if (!cmd.hasOption("prove")) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a rl file!.", "command line", "Command line arguments."));
            //} else {
                //GlobalSettings.CHECK = new File(cmd.getOptionValue("prove")).getAbsolutePath();
            //}


            String def = null;
            //if (cmd.hasOption("definition"))
            //    def = cmd.getOptionValue("definition");
            //else {
            //    String[] restArgs = cmd.getArgs();
            //    if (restArgs.length < 1)
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a file in order to compile!.", "command line", "System file."));
            //    else
            //        def = restArgs[0];
            //}

            //GlobalSettings.setMainFile(def);

            String lang = null;//FileUtil.getMainModule(GlobalSettings.mainFile.getName());

            // Matching Logic & Symbolic Calculus options
            //GlobalSettings.symbolicEquality = true;
            //GlobalSettings.SMT = true;

            Context context = null;//new Context();

            if (context.dotk == null) {
                //try {
                //    context.dotk = new File(GlobalSettings.mainFile.getCanonicalFile().getParent() + File.separator + ".k");
                //} catch (IOException e) {
                //    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Canonical file cannot be obtained for main file.", GlobalSettings.mainFile.getAbsolutePath(),
                //            "File system."));
                //}
                context.dotk.mkdirs();
            }

            Backend backend = new RLBackend(Stopwatch.instance(), context);
            //output = FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + "-kompiled";
            context.dotk.mkdirs();

            genericCompile(lang, backend, null, context);
            //BinaryLoader.save(context.dotk.getAbsolutePath() + "/compile-options.bin", cmd, context);

            //verbose(cmd, context);
        //}

        return true;
    }

    //public static void verbose(CommandLine cmd, Context context) {
        //Stopwatch.instance().printTotal("Total");
        //if (GlobalSettings.verbose) {
            //context.printStatistics();
        //}
    //}


    public static void genericCompile(
            String lang,
            Backend backend,
            String step,
            Context context) {
        org.kframework.kil.Definition javaDef;
        Stopwatch.instance().start();
        javaDef = null;//DefinitionLoader.loadDefinition(GlobalSettings.mainFile, lang, backend.autoinclude(), context);
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

        BinaryLoader.saveOrDie(
                context.dotk.getAbsolutePath() + "/configuration.bin", MetaK.getConfiguration(javaDef, context));
        backend.run(javaDef);
    }
}
