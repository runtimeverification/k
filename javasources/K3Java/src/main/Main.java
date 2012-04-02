package main;

import java.io.*;
import k.utils.*;
import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		OptionsParser op = new OptionsParser();

		CommandLine cmd = op.parse(args);

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		// set lib if any
		if (cmd.hasOption("lib"))
		{
			GlobalSettings.lib = cmd.getOptionValue("lib");
		}
		
		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		} else if (cmd.hasOption("maudify")) {
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
			if (!mainFile.exists())
				k.utils.Error.report("Could not find file: " + def);

			String lang = null;
			if (cmd.hasOption("lang"))
				lang = cmd.getOptionValue("lang");
			else
				lang = mainFile.getName().substring(0, mainFile.getName().length() - 2).toUpperCase();
			FrontEnd.maudify(mainFile, lang);
		} else if (cmd.hasOption("compile")) {
			String file = null;
			if (cmd.hasOption("file"))
				file = cmd.getOptionValue("file");
			else {
				String[] restArgs = cmd.getArgs();
				if (restArgs.length < 1)
					k.utils.Error.report("You have to provide a file in order to compile!.");
				else
					file = restArgs[0];
			}

			File mainFile = new File(file);
			if (!mainFile.exists())
				k.utils.Error.report("Could not find file: " + file);

			String lang = null;
			if (cmd.hasOption("lang"))
				lang = cmd.getOptionValue("lang");
			else
				lang = mainFile.getName().substring(0, mainFile.getName().length() - 2).toUpperCase();
			FrontEnd.compile(mainFile, lang);
		} else if (cmd.hasOption("kast")) {
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
				// def = mainFile.getName().substring(0, mainFile.getName().length() - 2).toUpperCase();
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
			FrontEnd.parsePgm(mainFile, def);
			// } else if (cmd.hasOption("latex") && cmd.hasOption("file")) {
			// latex(cmd);
		}
	}
}
