package org.kframework.main;

import com.thoughtworks.xstream.XStream;
import org.apache.commons.cli.CommandLine;
import org.kframework.backend.Backend;
import org.kframework.backend.doc.DocumentationBackend;
import org.kframework.backend.html.HtmlBackend;
import org.kframework.backend.kil.KExpBackend;
import org.kframework.backend.latex.LatexBackend;
import org.kframework.backend.latex.PdfBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.unparser.UnparserBackend;
import org.kframework.backend.xml.XmlBackend;
import org.kframework.compile.AddEval;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.AutomaticModuleImportsTransformer;
import org.kframework.compile.sharing.DittoFilter;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.FunctionalAdaptor;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kompile.lint.InfiniteRewrite;
import org.kframework.kompile.lint.KlintRule;
import org.kframework.kompile.lint.UnusedName;
import org.kframework.kompile.lint.UnusedSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class KompileFrontEnd {

	private static String output;

	private static List<String> metadataParse(String tags) {
		String[] alltags = tags.split("\\s+");
		List<String> result = new ArrayList<String>();
		for (int i = 0; i < alltags.length; i++)
			result.add(alltags[i]);
		return result;
	}

	public static void kompile(String[] args) {
		KompileOptionsParser op = new KompileOptionsParser();

		CommandLine cmd = op.parse(args);

		// options: help
		if (cmd.hasOption("help"))
			org.kframework.utils.Error.helpExit(op.getHelp(), op.getOptions());

		if (cmd.hasOption("version")) {
			String msg = FileUtil.getFileContent(KPaths.getKBase(false) + "/bin/version.txt");
			System.out.println(msg);
			System.exit(0);
		}

		// set verbose
		if (cmd.hasOption("verbose"))
			GlobalSettings.verbose = true;

		if (cmd.hasOption("nofilename"))
			GlobalSettings.noFilename = true;

		if (cmd.hasOption("warnings"))
			GlobalSettings.hiddenWarnings = true;

		if (cmd.hasOption("transition"))
			GlobalSettings.transition = metadataParse(cmd.getOptionValue("transition"));
		if (cmd.hasOption("supercool"))
			GlobalSettings.supercool = metadataParse(cmd.getOptionValue("supercool"));
		if (cmd.hasOption("superheat"))
			GlobalSettings.superheat = metadataParse(cmd.getOptionValue("superheat"));

		if (cmd.hasOption("style")) {
			String style = cmd.getOptionValue("style");
			if (style.startsWith("+")) {
				GlobalSettings.style += style.replace("+", ",");
			} else {
				GlobalSettings.style = style;
			}
		}

		if (cmd.hasOption("addTopCell"))
			GlobalSettings.addTopCell = true;

		// set lib if any
		if (cmd.hasOption("lib")) {
			GlobalSettings.lib = cmd.getOptionValue("lib");
		}
		if (cmd.hasOption("syntax-module"))
			GlobalSettings.synModule = cmd.getOptionValue("syntax-module");

		String step = null;
		if (cmd.hasOption("step")) {
			step = cmd.getOptionValue("step");
		}

		if (cmd.hasOption("fromxml")) {
			// File xmlFile = new File(cmd.getOptionValue("fromxml"));
			// if (cmd.hasOption("lang"))
			// fromxml(xmlFile, cmd.getOptionValue("lang"), step);
			// else
			// fromxml(xmlFile, FileUtil.getMainModule(xmlFile.getName()), step);
			System.err.println("fromxml option not supported anymore");
			System.exit(0);
		}

		String def = null;
		if (cmd.hasOption("def"))
			def = cmd.getOptionValue("def");
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
			if (!mainFile.exists())
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "File: " + errorFile.getName() + "(.k) not found.", errorFile.getAbsolutePath(),
						"File system."));
		}

		output = null;
		if (cmd.hasOption("output")) {
			output = cmd.getOptionValue("output");
		}

		String lang = null;
		if (cmd.hasOption("lang"))
			lang = cmd.getOptionValue("lang");
		else
			lang = FileUtil.getMainModule(mainFile.getName());

		if (cmd.hasOption("lint")) {
			lint(mainFile, lang);
		}

		Backend backend = null;
		if (cmd.hasOption("maudify")) {
			backend = new MaudeBackend(Stopwatch.sw);
		} else if (cmd.hasOption("latex")) {
			backend = new LatexBackend(Stopwatch.sw);
		} else if (cmd.hasOption("pdf")) {
			backend = new PdfBackend(Stopwatch.sw);
		} else if (cmd.hasOption("xml")) {
			backend = new XmlBackend(Stopwatch.sw);
		} else if (cmd.hasOption("html")) {
			backend = new HtmlBackend(Stopwatch.sw);
		} else if (cmd.hasOption("unparse")) {
			backend = new UnparserBackend(Stopwatch.sw);
		}  else if (cmd.hasOption("kexp")) {
			backend = new KExpBackend(Stopwatch.sw);
		} else if (cmd.hasOption("doc")) {
			backend = new DocumentationBackend(Stopwatch.sw);
		} else {
			if (output == null) {
				try {
					output = mainFile.getCanonicalFile().getParent() + File.separator + FileUtil.stripExtension(mainFile.getName()) + "-kompiled";
				} catch (IOException e) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
							"Canonical file cannot be obtained for main file.",
							mainFile.getAbsolutePath(), "File system."));
				}
			}
			backend = new KompileBackend(Stopwatch.sw);
		}
		initializeDotK(mainFile);
		if (backend != null) {
			genericCompile(mainFile, lang, backend, step);
		}
		if (GlobalSettings.verbose)
			Stopwatch.sw.printTotal("Total");
		GlobalSettings.kem.print();
	}

	private static void initializeDotK(File mainFile) {
		String output = KompileFrontEnd.output;
		if (output==null) {
			try {
				output = mainFile.getCanonicalFile().getParent() + File.separator + ".k";
			} catch (IOException e) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
						"Canonical file cannot be obtained for main file.",
						mainFile.getAbsolutePath(), "File system."));
			}
		}
		DefinitionHelper.dotk = new File(output);
		DefinitionHelper.dotk.mkdirs();
	}

	private static void genericCompile(File mainFile, String lang, Backend backend, String step) {
		org.kframework.kil.Definition javaDef;
		try {
			Stopwatch.sw.Start();
			javaDef = org.kframework.utils.DefinitionLoader.loadDefinition(mainFile, lang, backend.autoinclude());
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(javaDef);

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/defx.xml", xml);

			if (GlobalSettings.verbose) {
				Stopwatch.sw.printIntermediate("Serialize Definition to XML");
			}

			CompilerSteps<Definition> steps = new CompilerSteps<Definition>();
			if (GlobalSettings.verbose) {
				steps.setSw(Stopwatch.sw);
			}
			steps.add(new FirstStep(backend));
			steps.add(new RemoveBrackets());
			steps.add(new AddEmptyLists());
			steps.add(new CheckVisitorStep(new CheckVariables()));
			steps.add(new CheckVisitorStep(new CheckRewrite()));
			steps.add(new AutomaticModuleImportsTransformer());
			steps.add(new FunctionalAdaptor(new DittoFilter()));
			steps.add(new FlattenModules());
			steps.add(new StrictnessToContexts());
			steps.add(new FreezeUserFreezers());
			steps.add(new ContextsToHeating());
			steps.add(new AddSupercoolDefinition());
			steps.add(new AddHeatingConditions());
			steps.add(new AddSuperheatRules());
			steps.add(new DesugarStreams());
			steps.add(new ResolveFunctions());
			steps.add(new AddKCell());
			steps.add(new AddSymbolicK());
			// steps.add(new ResolveFresh());
			steps.add(new ResolveFreshMOS());
			steps.add(new AddTopCellConfig());
			if (GlobalSettings.addTopCell) {
				steps.add(new AddTopCellRules());
			}
			steps.add(new AddEval());
			steps.add(new ResolveBinder());
			steps.add(new ResolveAnonymousVariables());
			steps.add(new ResolveBlockingInput());
			steps.add(new AddK2SMTLib());
			steps.add(new AddPredicates());
			steps.add(new ResolveSyntaxPredicates());
			steps.add(new ResolveBuiltins());
			steps.add(new ResolveListOfK());
			steps.add(new FlattenSyntax());
			steps.add(new AddKLabelToString());
			steps.add(new AddKLabelConstant());
			steps.add(new ResolveHybrid());
			steps.add(new ResolveConfigurationAbstraction());
			steps.add(new ResolveOpenCells());
			steps.add(new ResolveRewrite());
			steps.add(new ResolveSupercool());
			steps.add(new AddStrictStar());
			steps.add(new AddDefaultComputational());
			steps.add(new AddOptionalTags());
			steps.add(new LastStep(backend));

			if (step == null) {
				step = backend.getDefaultStep();
			}
			try {
				javaDef = steps.compile(javaDef, step);
			} catch (CompilerStepDone e) {
				javaDef = (Definition) e.getResult();
			}
			backend.run(javaDef);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private static void lint(File mainFile, String mainModule) {
		try {
			File canonicalFile = mainFile.getCanonicalFile();
			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(canonicalFile, mainModule, true);

			KlintRule lintRule = new UnusedName(javaDef);
			lintRule.run();

			lintRule = new UnusedSyntax(javaDef);
			lintRule.run();

			lintRule = new InfiniteRewrite(javaDef);
			lintRule.run();
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e1) {
			e1.printStackTrace();
		}
	}

	// public static void pdfClean(String[] extensions) {
	// for (int i = 0; i < extensions.length; i++)
	// new File(GlobalSettings.mainFileWithNoExtension + extensions[i]).delete();
	// }

}
