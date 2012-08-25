package main;

import java.io.File;
import java.io.IOException;

import k.utils.FileUtil;
import k.utils.KPaths;
import k.utils.Stopwatch;
import k.utils.XmlLoader;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class KastFrontEnd {

	public static void kast(String[] args) {
		Stopwatch sw = new Stopwatch();
		KastOptionsParser op = new KastOptionsParser();
		CommandLine cmd = op.parse(args);

		if (cmd.hasOption("version")) {
			String msg = FileUtil.getFileContent(KPaths.getKBase(false) + "/bin/version.txt");
			System.out.println(msg);
			System.exit(0);
		}

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		if (cmd.hasOption("nofilename")) {
			GlobalSettings.noFilename = true;
		}
		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		}
		String pgm = null;
		if (cmd.hasOption("pgm"))
			pgm = cmd.getOptionValue("pgm");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a file in order to kast a program!.", "command line", "System file.", 0));
			else
				pgm = restArgs[0];
		}

		File mainFile = new File(pgm);
		if (!mainFile.exists())
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file.", 0));

		File def = null;
		if (cmd.hasOption("def")) {
			def = new File(cmd.getOptionValue("def"));
			if (!def.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file.", 0));
		} else {
			// search for the definition
			try {
				File pgmFolder = new File(".").getCanonicalFile();
				boolean found = false;
				while (!found) {
					// check to see if I got to / or drive folder
					if (pgmFolder.getAbsoluteFile().getParentFile() == null)
						break;
					File dotk = new File(pgmFolder.getCanonicalPath() + "/.k");
					pgmFolder = pgmFolder.getParentFile();
					if (dotk.exists()) {
						File defXml = new File(dotk.getCanonicalPath() + "/def.xml");
						if (!defXml.exists()) {
							GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find the compiled definition in: " + dotk, "command line", pgm, 0));
						}

						Document doc = XmlLoader.getXMLDoc(FileUtil.getFileContent(defXml.getAbsolutePath()));
						Element el = (Element) doc.getElementsByTagName("def").item(0);
						def = new File(el.getAttribute("mainFile"));
						found = true;
					}
				}

				if (def == null)
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find a compiled definition, please provide one using the -def option", "command line", pgm, 0));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		k.utils.ProgramLoader.processPgm(mainFile, def);
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print();
	}
}
