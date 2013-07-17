package org.kframework.kast;

import java.io.File;
import java.io.FileInputStream;
import java.io.FilenameFilter;
import java.io.IOException;

import org.apache.commons.cli.CommandLine;
import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.IndentationOptions;
import org.kframework.backend.unparser.KastFilter;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class KastFrontEnd {

	public static void kast(String[] args) {
		Context context = new Context();
		Stopwatch sw = new Stopwatch();
		KastOptionsParser op = new KastOptionsParser();
		CommandLine cmd = op.parse(args);

		if (cmd.hasOption("version")) {
			String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
			System.out.println(msg);
			System.exit(0);
		}

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		// set fast kast option
		if (cmd.hasOption("fastKast")) {
			GlobalSettings.fastKast = true;
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
		} else if (cmd.hasOption("binaryParser")) {
			GlobalSettings.whatParser = GlobalSettings.ParserType.BINARY;
			path = new File(cmd.getOptionValue("binaryParser")).getAbsolutePath();
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
			File mainFile = new File(pgm);
			path = mainFile.getAbsolutePath();
			if (!mainFile.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));
			pgm = FileUtil.getFileContent(mainFile.getAbsolutePath());
		}

		File def = null;
		org.kframework.kil.Definition javaDef = null;
		if (cmd.hasOption("k-definition")) {
			def = new File(cmd.getOptionValue("k-definition"));
			if (!def.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find file: " + pgm, "command line", "System file."));
			if (context.kompiled == null) {
				try {
					String fileName = FileUtil.stripExtension(def.getName());
					context.kompiled = new File(def.getCanonicalFile().getParent() + File.separator + fileName + "-kompiled");
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		} else if (cmd.hasOption("compiled-def")) {
			context.kompiled = new File(cmd.getOptionValue("compiled-def"));
			if (!context.kompiled.exists()) {
				String msg = "Could not find directory: " + context.kompiled;
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", context.kompiled.getAbsolutePath()));
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
					if (context.kompiled != null) {
						String msg = "Multiple compiled definitions found. Use -kDefinition or -compiledDef to specify one.";
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
					} else {
						context.kompiled = new File(dirs[i]).getAbsoluteFile();
					}
				}
			}
			if (context.kompiled == null && System.getenv("KRUN_COMPILED_DEF") != null) {
				context.kompiled = new File(System.getenv("KRUN_COMPILED_DEF"));
			}

			if (context.kompiled == null) {
				String msg = "Could not find a compiled definition. Use -kDefinition or -compiledDef to specify one.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
			}
		}
		try {
			if (context.kompiled.exists()) {
				File defXml = new File(context.kompiled.getCanonicalPath() + "/defx.bin");
				if (!defXml.exists()) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Could not find the compiled definition.", "command line",
							defXml.getAbsolutePath()));
				}

				javaDef = (org.kframework.kil.Definition) BinaryLoader.fromBinary(new FileInputStream(defXml));
				javaDef = new FlattenModules(context).compile(javaDef, null);
				javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddTopCellConfig(
                        context));
				// This is essential for generating maude
				javaDef.preprocess(context);

				def = new File(javaDef.getMainFile());
			} else {
				String msg = "Could not find a valid compiled definition. Use -kDefinition or -compiledDef to specify one.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", new File(".").getAbsolutePath()));
			}
		} catch (IOException e) {
			e.printStackTrace();
		} catch (TransformerException e) {
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
		if (cmd.hasOption("groundParser")) {
			GlobalSettings.whatParser = GlobalSettings.ParserType.GROUND;
		}

		String sort = context.startSymbolPgm;
		if (System.getenv("KRUN_SORT") != null) {
			sort = System.getenv("KRUN_SORT");
		}
		if (cmd.hasOption("sort")) {
			sort = cmd.getOptionValue("sort");
		}

		try {
			ASTNode out = ProgramLoader.processPgm(pgm, path, javaDef, sort, context, GlobalSettings.whatParser);
			String kast;
			if (prettyPrint) {
				KastFilter kastFilter = new KastFilter(indentationOptions, nextline, context);
				out.accept(kastFilter);
				kast = kastFilter.getResult();
			} else {
				MaudeFilter maudeFilter = new MaudeFilter(context);
				out.accept(maudeFilter);
				kast = maudeFilter.getResult();
			}
			System.out.println(kast);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify Program");
				sw.printTotal("Total");
			}
			GlobalSettings.kem.print();
		} catch (TransformerException e) {
			e.report();
		}
	}
}
