package org.kframework.main;

import java.io.File;
import java.io.FilenameFilter;
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
		String path;
		if (cmd.hasOption("e")) {
			pgm = cmd.getOptionValue("e");
			path = "Command line";
		} else {
			if (cmd.hasOption("pgm")) {
				pgm = cmd.getOptionValue("pgm");
			} else {
				String[] restArgs = cmd.getArgs();
				if (restArgs.length < 1) {
					String msg = "You have to provide a file in order to kast a program!.";
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", "System file."));
				} else
					pgm = restArgs[0];
			}
			path = pgm;
			File mainFile = new File(pgm);
			if (!mainFile.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));
			pgm = FileUtil.getFileContent(mainFile.getAbsolutePath());
		}

		File def = null;
		org.kframework.kil.Definition javaDef = null;
		if (cmd.hasOption("kDefinition")) {
			def = new File(cmd.getOptionValue("kDefinition"));
			if (!def.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));
			if (DefinitionHelper.kompiled == null) {
				try {
					String fileName = FileUtil.stripExtension(def.getName());
					DefinitionHelper.kompiled = new File(def.getCanonicalFile().getParent() + File.separator + fileName + "-kompiled");
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		} else if (cmd.hasOption("compiledDef")) {
			DefinitionHelper.kompiled = new File(cmd.getOptionValue("compiledDef"));
			if (!DefinitionHelper.kompiled.exists()) {
				String msg = "Could not find directory: " + DefinitionHelper.kompiled;
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", DefinitionHelper.kompiled.getAbsolutePath()));
			}
		} else {
			// search for the definition
			String[] dirs = new File(".").list(new FilenameFilter() {
				@Override
				public boolean accept(File current, String name) {
					return new File(current, name).isDirectory();
				}
			});

			for (int i = 0; i < dirs.length; i++) {
				if (dirs[i].endsWith("-kompiled")) {
					if (DefinitionHelper.kompiled != null) {
						String msg = "Multiple compiled definitions found. Use -kDefinition or -compiledDef to specify one.";
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
					} else {
						DefinitionHelper.kompiled = new File(dirs[i]).getAbsoluteFile();
					}
				}
			}

			if (DefinitionHelper.kompiled == null) {
				String msg = "Could not find a compiled definition. Use -kDefinition or -compiledDef to specify one.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
			}
		}
		try {
			if (DefinitionHelper.kompiled.exists()) {
				File defXml = new File(DefinitionHelper.kompiled.getCanonicalPath() + "/defx.xml");
				if (!defXml.exists()) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find the compiled definition.", "command line", defXml.getAbsolutePath()));
				}

				XStream xstream = new XStream();
				xstream.aliasPackage("k", "ro.uaic.info.fmse.k");
				javaDef = (org.kframework.kil.Definition) xstream.fromXML(defXml);
				// This is essential for generating maude
				javaDef.preprocess();

				def = new File(javaDef.getMainFile());
			} else {
				String msg = "Could not find a valid compiled definition. Use -kDefinition or -compiledDef to specify one.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
			}
		} catch (IOException e) {
			e.printStackTrace();
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

		if (cmd.hasOption("ruleParser")) {
			GlobalSettings.whatParser = GlobalSettings.ParserType.RULES;
		}
		if (cmd.hasOption("concreteParser")) {
			GlobalSettings.whatParser = GlobalSettings.ParserType.GROUND;
		}
		System.out.println(org.kframework.utils.ProgramLoader.processPgm(pgm, path, javaDef, prettyPrint, nextline, indentationOptions));
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print();
	}
}
