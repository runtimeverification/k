package main;

import java.io.File;
import java.io.IOException;

import k.utils.ProgramLoader;
import k.utils.FileUtil;
import k.utils.Stopwatch;
import k.utils.XmlLoader;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.general.GlobalSettings;

public class KastFrontEnd {

	public static void kast(String[] args) {
		Stopwatch sw = new Stopwatch();
		KastOptionsParser op = new KastOptionsParser();
		CommandLine cmd = op.parse(args);
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
				k.utils.Error.report("You have to provide a file in order to kast a program!.");
			else
				pgm = restArgs[0];
		}

		File mainFile = new File(pgm);
		if (!mainFile.exists())
			k.utils.Error.report("Could not find file: " + pgm);

		File def = null;
		if (cmd.hasOption("def")) {
			def = new File(cmd.getOptionValue("def"));
			if (!def.exists())
				k.utils.Error.report("Could not find file: " + def);
		} else {
			// search for the definition
			try {
				File pgmFolder = mainFile.getCanonicalFile();
				boolean found = false;
				while (!found) {
					// check to see if I got to / or drive folder
					if (pgmFolder.getAbsoluteFile().getParentFile() == null)
						break;
					File dotk = new File(pgmFolder.getParent() + "/.k");
					pgmFolder = pgmFolder.getParentFile();
					if (dotk.exists()) {
						File defXml = new File(dotk.getCanonicalPath() + "/def.xml");
						if (!defXml.exists()) {
							k.utils.Error.report("Could not find the compiled definition in: " + dotk);
						}

						Document doc = XmlLoader.getXMLDoc(FileUtil.getFileContent(defXml.getAbsolutePath()));
						Element el = (Element) doc.getElementsByTagName("def").item(0);
						def = new File(el.getAttribute("mainFile"));
						found = true;
					}
				}

				if (def == null)
					k.utils.Error.report("Could not find a compiled definition, please provide one using the -def option");
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		k.utils.ProgramLoader.parsePgm(mainFile, def, GlobalSettings.verbose);
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
	}
}
