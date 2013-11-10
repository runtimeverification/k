package org.kframework.kcheck;

import java.io.File;
import java.io.IOException;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.CountNodesVisitor;
import org.kframework.parser.DefinitionLoader;
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
	
	public static void kcheck(String[] args) {
			KCheckOptionsParser op = new KCheckOptionsParser();

			CommandLine cmd = op.parse(args);

			// options: help
			if (cmd.hasOption("help"))
				org.kframework.utils.Error.helpExit(op.getHelp(), op.getOptions());

			if (cmd.hasOption("version")) {
				String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
				System.out.println(msg);
				System.exit(0);
			}

	        GlobalSettings.symbolicEquality = true;
	        GlobalSettings.SMT = true;
	        GlobalSettings.NOSMT = false;
	        RLBackend.SIMPLIFY = cmd.hasOption("simplify");
	        
	        if (cmd.hasOption("pgm")) {
	        	RLBackend.PGM = cmd.getOptionValue("pgm");
	        }
	        
			// set verbose
			if (cmd.hasOption("verbose"))
				GlobalSettings.verbose = true;

			GlobalSettings.addTopCell = true;

			if (!cmd.hasOption("prove")) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a rl file!.", "command line", "Command line arguments."));
			}else {
				GlobalSettings.CHECK = new File(cmd.getOptionValue("prove")).getAbsolutePath();
			}
			

			String def = null;
			if (cmd.hasOption("definition"))
				def = cmd.getOptionValue("definition");
			else {
				String[] restArgs = cmd.getArgs();
				if (restArgs.length < 1)
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a file in order to compile!.", "command line", "System file."));
				else
					def = restArgs[0];
			}

			File mainFile = new File(def);
			GlobalSettings.mainFile = mainFile;
			GlobalSettings.mainFileWithNoExtension = mainFile.getAbsolutePath().replaceFirst("\\.k$", "").replaceFirst("\\.xml$", "");
			if (!mainFile.exists()) {
				File errorFile = mainFile;
				mainFile = new File(def + ".k");
				if (!mainFile.exists()) {
					String msg = "File: " + errorFile.getName() + "(.k) not found.";
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
				}
			}

			String lang = FileUtil.getMainModule(mainFile.getName());

			// Matching Logic & Symbolic Calculus options
			GlobalSettings.symbolicEquality = true;
			GlobalSettings.SMT = true;
			
			Context context = new Context();
			
			if (context.dotk == null) {
				try {
					context.dotk = new File(mainFile.getCanonicalFile().getParent() + File.separator + ".k");
				} catch (IOException e) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Canonical file cannot be obtained for main file.", mainFile.getAbsolutePath(),
							"File system."));
				}
				context.dotk.mkdirs();
			}

			Backend backend = new RLBackend(Stopwatch.sw, context);
        output = FilenameUtils.removeExtension(mainFile.getName()) + "-kompiled";
			context.dotk = new File(output);
			context.dotk.mkdirs();

			genericCompile(mainFile, lang, backend, null, context);
        BinaryLoader.save(context.dotk.getAbsolutePath() + "/compile-options.bin", cmd);

        verbose(cmd, context);
	}
	private static void verbose(CommandLine cmd, Context context) {
		if (GlobalSettings.verbose) {
			Stopwatch.sw.printTotal("Total");
            context.printStatistics();
        }
		GlobalSettings.kem.print();
	}


	private static void genericCompile(
            File mainFile,
            String lang,
            Backend backend,
            String step,
            Context context) {
		org.kframework.kil.Definition javaDef;
		try {
			Stopwatch.sw.Start();
			javaDef = DefinitionLoader.loadDefinition(mainFile, lang, backend.autoinclude(), context);
            javaDef.accept(new CountNodesVisitor(context));

			CompilerSteps<Definition> steps = backend.getCompilationSteps();

			if (GlobalSettings.verbose) {
				steps.setSw(Stopwatch.sw);
			}
			if (step == null) {
				step = backend.getDefaultStep();
			}
			try {
				javaDef = steps.compile(javaDef, step);
			} catch (CompilerStepDone e) {
				javaDef = (Definition) e.getResult();
			}

            BinaryLoader.save(
                context.dotk.getAbsolutePath() + "/configuration.bin", MetaK.getConfiguration(javaDef, context)
            );

			backend.run(javaDef);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
