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
import ro.uaic.info.fmse.hkcd.HaskellDumpFilter;

/// Haskell K Compiler dump tool frontend
///
/// @todo .def loading routine is the same as in kompile — refactor it
/// as well
public class HKCDFrontEnd {

	public static void hkcd(String[] args) {
		Stopwatch sw = new Stopwatch();
		KompileOptionsParser op = new KompileOptionsParser();

		CommandLine cmd = op.parse(args);

		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		}

		// // set verbose
		// if (cmd.hasOption("verbose")) {
		//	GlobalSettings.verbose = true;
		// }

		String def = null;
		if (cmd.hasOption("def"))
			def = cmd.getOptionValue("def");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				k.utils.Error.report("You have to provide a file in order to compile!.");
			else
				def = restArgs[0];
		}

		File mainFile = new File(def);
		GlobalSettings.mainFile = mainFile;
		GlobalSettings.mainFileWithNoExtension = mainFile.getAbsolutePath().replaceFirst("\\.k$", "").replaceFirst("\\.xml$", "");
		if (!mainFile.exists()) {
			File errorFile = mainFile;
			mainFile = new File(def + ".k");
			if (!mainFile.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "File: " + errorFile.getName() + "(.k) not found.", errorFile.getAbsolutePath(), "File system.", 0));
		}

		String lang = null;
		if (cmd.hasOption("lang"))
			lang = cmd.getOptionValue("lang");
		else
			lang = mainFile.getName().replaceFirst("\\.[a-zA-Z]+$", "").toUpperCase();

		hkcd(mainFile, lang);

		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print(GlobalSettings.level);
	}


	public static String hkcd(File mainFile, String mainModule) {
		try {
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			String fileSep = System.getProperty("file.separator");
			File dotk = new File(canonicalFile.getParent() + fileSep + ".k");
			dotk.mkdirs();

			GlobalSettings.latex = true;

			ro.uaic.info.fmse.k.Definition javaDef = k.utils.DefinitionLoader.loadDefinition(mainFile, mainModule, GlobalSettings.verbose);

			Stopwatch sw = new Stopwatch();

			HaskellDumpFilter hdf = new HaskellDumpFilter();
			javaDef.accept(hdf);

			String dumped = hdf.getResult();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.hkcd", dumped);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".hkcd", dumped);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("HKCD         = ");
			}

			return dumped;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}
}
