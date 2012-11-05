package org.kframework.main;

import java.io.File;
import java.io.IOException;

import org.apache.commons.cli.CommandLine;
import org.kframework.backend.unparser.IndentationOptions;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import com.thoughtworks.xstream.XStream;

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
			org.kframework.utils.Error.helpExit(op.getHelp(), op.getOptions());
		}
		String pgm = null;
		if (cmd.hasOption("pgm"))
			pgm = cmd.getOptionValue("pgm");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a file in order to kast a program!.", "command line", "System file."));
			else
				pgm = restArgs[0];
		}

		File mainFile = new File(pgm);
		if (!mainFile.exists())
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));

		File def = null;
		org.kframework.kil.Definition javaDef = null;
		if (cmd.hasOption("def")) {
			def = new File(cmd.getOptionValue("def"));
			if (!def.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));
			if (DefinitionHelper.dotk == null) {
				try {
					DefinitionHelper.dotk = new File(def.getCanonicalFile().getParent() + File.separator + ".k");
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		} else {
			// search for the definition
			try {
				// check to see if I got to / or drive folder
				if (DefinitionHelper.dotk == null) {
					DefinitionHelper.dotk = new File(new File(".").getCanonicalPath() + "/.k");
				}
				if (DefinitionHelper.dotk.exists()) {
					File defXml = new File(DefinitionHelper.dotk.getCanonicalPath() + "/defx.xml");
					if (!defXml.exists()) {
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find the compiled definition.", "command line", defXml.getAbsolutePath()));
					}

					XStream xstream = new XStream();
					xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

					javaDef = (org.kframework.kil.Definition) xstream.fromXML(defXml);
					// This is essential for generating maude
					javaDef.preprocess();

					def = new File(javaDef.getMainFile());
				}

				if (def == null)
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find a compiled definition, please provide one using the -def option", "command line", pgm));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		boolean prettyPrint = false;
		boolean nextline = false;
		IndentationOptions indentationOptions = new IndentationOptions();
		if (cmd.hasOption("pretty")) {
			prettyPrint = true;
			if (cmd.hasOption("tabsize")) {
				indentationOptions.setTabSize(new Integer(cmd.getOptionValue("tabsize")));
			} else {
				indentationOptions.setTabSize(4);
			}
			if (cmd.hasOption("maxwidth")) {
				indentationOptions.setWidth(new Integer(cmd.getOptionValue("maxwidth")));
			} else {
				indentationOptions.setWidth(Integer.MAX_VALUE);
			}
			if (cmd.hasOption("auxtabsize")) {
				indentationOptions.setAuxTabSize(new Integer(cmd.getOptionValue("auxtabsize")));
			}
			if (cmd.hasOption("nextline")) {
				nextline = true;
			}
		}

		org.kframework.utils.ProgramLoader.processPgm(mainFile, javaDef, prettyPrint, nextline, indentationOptions);
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print();
	}
}
