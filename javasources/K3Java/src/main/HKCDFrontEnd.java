package main;

import java.io.File;
import java.io.IOException;

import k.utils.Stopwatch;

import org.apache.commons.cli.CommandLine;
import org.kframework.backend.hkcd.HaskellDefFilter;
import org.kframework.backend.hkcd.HaskellPgmFilter;
import org.kframework.kil.ASTNode;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

import ro.uaic.info.fmse.utils.file.FileUtil;

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
	public static void hkcd(File defFile, File pgmFile, String mainModule) {
		try {
			Stopwatch sw = new Stopwatch();
			String fileSep = System.getProperty("file.separator");

			File defCanonical = defFile.getCanonicalFile();
			File pgmCanonical = pgmFile.getCanonicalFile();
			File dotk = new File(defCanonical.getParent() + fileSep + ".k");
			dotk.mkdirs();

			GlobalSettings.literate = true;

			org.kframework.kil.Definition langDef =
				k.utils.DefinitionLoader.loadDefinition(
					defFile,
					mainModule);

			ASTNode pgmAst = 
				k.utils.ProgramLoader.loadPgmAst(
					pgmFile, dotk, false);

			HaskellPgmFilter hpf = new HaskellPgmFilter();
			pgmAst.accept(hpf);
			String pgmDump = hpf.getResult();

			HaskellDefFilter hdf = new HaskellDefFilter();
			langDef.accept(hdf);
			String defDump = hdf.getResult();

			System.out.println("Definition:");
			System.out.println(defDump);

			System.out.println("Program:");
			System.out.println(pgmDump);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm.hkcd", pgmDump);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.hkcd", defDump);

			FileUtil.saveInFile(
				FileUtil.stripExtension(defCanonical.getAbsolutePath()) +
				".hkcd",
				defDump);

			FileUtil.saveInFile(
				FileUtil.stripExtension(pgmCanonical.getAbsolutePath()) +
				".hkcd",
				pgmDump);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("HKCD         = ");
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
