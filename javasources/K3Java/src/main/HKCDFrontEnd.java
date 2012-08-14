package main;

import java.io.File;
import java.io.IOException;

import k.utils.FileUtil;
import k.utils.Stopwatch;

import org.apache.commons.cli.CommandLine;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.hkcd.HaskellPgmFilter;

import ro.uaic.info.fmse.k.ASTNode;

/**
 * Haskell K Compiler dump tool frontend
 *
 * @todo .def and .pgm loading routines is the same as in
 * kast/kompile — refactor it as well
 */
public class HKCDFrontEnd {

	public static void hkcd(String[] args) {
		Stopwatch sw = new Stopwatch();
		HKCDOptionsParser op = new HKCDOptionsParser();

		CommandLine cmd = op.parse(args);

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), "hkcd DEF PGM", op.getOptions());
		}

		String def = null;
		if (cmd.hasOption("def"))
			def = cmd.getOptionValue("def");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				GlobalSettings.kem.register(
					new KException(ExceptionType.ERROR,
						       KExceptionGroup.CRITICAL,
						       "You have to provide a language definition in order to compile!",
						       "command line",
						       "System file.", 0));
			else
				def = restArgs[0];
		}

		// Load .def
		File defFile = new File(def);
		GlobalSettings.mainFile = defFile;
		GlobalSettings.mainFileWithNoExtension =
			defFile.getAbsolutePath().replaceFirst("\\.k$", "").replaceFirst("\\.xml$", "");
		if (!defFile.exists()) {
			File errorFile = defFile;
			defFile = new File(def + ".k");
			if (!defFile.exists())
				GlobalSettings.kem.register(
					new KException(ExceptionType.ERROR,
						       KExceptionGroup.CRITICAL,
						       "File: " + errorFile.getName() + "(.k) not found.",
						       errorFile.getAbsolutePath(), "File system.", 0));
		}

		// Load .pgm
		String pgm = null;
		if (cmd.hasOption("pgm"))
			pgm = cmd.getOptionValue("pgm");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 2)
				GlobalSettings.kem.register(
					new KException(ExceptionType.ERROR,
						       KExceptionGroup.CRITICAL,
						       "You have to provide a program source!",
						       "command line",
						       "System file.", 0));
			else
				pgm = restArgs[1];
		}

		File pgmFile = new File(pgm);
		if (!pgmFile.exists())
			k.utils.Error.report("Could not find file: " + pgm);

		String lang = null;
		if (cmd.hasOption("lang"))
			lang = cmd.getOptionValue("lang");
		else
			lang = FileUtil.getMainModule(defFile.getName());

		/// Do the actual processing
		hkcd(defFile, pgmFile, lang);

		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print();
	}


	/**
	 * Dump language definition and program tree to hkc-readable
	 * form
	 */
	public static String hkcd(File defFile, File pgmFile, String mainModule) {
		try {
			// for now just use this file as main argument
			File canonicalFile = defFile.getCanonicalFile();

			String fileSep = System.getProperty("file.separator");
			File dotk = new File(canonicalFile.getParent() + fileSep + ".k");
			dotk.mkdirs();

			GlobalSettings.literate = true;

			ro.uaic.info.fmse.k.Definition langDef =
				k.utils.DefinitionLoader.loadDefinition(
					defFile,
					mainModule,
					GlobalSettings.verbose);

			Stopwatch sw = new Stopwatch();

			HaskellPgmFilter hdf = new HaskellPgmFilter();

			ASTNode pgmAst = k.utils.ProgramLoader.loadPgmAst(pgmFile, dotk, false);

			pgmAst.accept(hdf);
			String dump = hdf.getResult();

			System.out.println(dump);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.hkcd", dump);

			FileUtil.saveInFile(
				FileUtil.stripExtension(canonicalFile.getAbsolutePath()) +
				".hkcd",
				dump);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("HKCD         = ");
			}

			return dump;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}
}
