package org.kframework.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.apache.commons.cli.CommandLine;
import org.kframework.backend.html.HTMLFilter;
import org.kframework.backend.latex.LatexFilter;
import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.AddEval;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.sharing.AutomaticModuleImportsTransformer;
import org.kframework.compile.sharing.DittoFilter;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.AddTopCell;
import org.kframework.compile.transformers.DesugarStreams;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.GenerateSyntaxPredicates;
import org.kframework.compile.transformers.GenerateSymbolicSyntaxPredicates;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveBinder;
import org.kframework.compile.transformers.ResolveBlockingInput;
import org.kframework.compile.transformers.ResolveBuiltins;
import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveDefaultTerms;
import org.kframework.compile.transformers.ResolveFresh;
import org.kframework.compile.transformers.ResolveFunctions;
import org.kframework.compile.transformers.ResolveHybrid;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveOpenCells;
import org.kframework.compile.transformers.ResolveSyntaxPredicates;
import org.kframework.compile.utils.CompilerTransformerStep;
import org.kframework.compile.utils.ConfigurationStructureVisitor;
import org.kframework.compile.utils.ConfigurationStructureVisitor.ConfigurationStructure;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.lint.InfiniteRewrite;
import org.kframework.kompile.lint.KlintRule;
import org.kframework.kompile.lint.UnusedName;
import org.kframework.kompile.lint.UnusedSyntax;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KMessages;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.maude.MaudeRun;
import org.kframework.utils.utils.file.FileUtil;
import org.kframework.utils.utils.file.KPaths;

import com.thoughtworks.xstream.XStream;

public class KompileFrontEnd {
	public static void kompile(String[] args) {
		Stopwatch sw = new Stopwatch();
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

		// set literate
		if (cmd.hasOption("literate"))
			GlobalSettings.literate = true;

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

		String step = "RESOLVE-HOOKS";
		if (cmd.hasOption("step"))
			step = cmd.getOptionValue("step");

		if (cmd.hasOption("fromxml")) {
			File xmlFile = new File(cmd.getOptionValue("fromxml"));
			if (cmd.hasOption("lang"))
				fromxml(xmlFile, cmd.getOptionValue("lang"), step);
			else
				fromxml(xmlFile, FileUtil.getMainModule(xmlFile.getName()), step);
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

		// DefinitionHelper.dotk = new File(mainFile.getCanonicalFile().getParent() + File.separator + FileUtil.stripExtension(mainFile.getName()) + "-compiled");
		if (DefinitionHelper.dotk == null) {
			try {
				DefinitionHelper.dotk = new File(mainFile.getCanonicalFile().getParent() + File.separator + ".k");
			} catch (IOException e) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Output dir cannot be used.", mainFile.getAbsolutePath(), "File system."));
			}
		}
		DefinitionHelper.dotk.mkdirs();

		String lang = null;
		if (cmd.hasOption("lang"))
			lang = cmd.getOptionValue("lang");
		else
			lang = FileUtil.getMainModule(mainFile.getName());

		if (cmd.hasOption("lint")) {
			lint(mainFile, lang);
		}

		if (cmd.hasOption("maudify")) {
			maudify(mainFile, lang);
		} else if (cmd.hasOption("latex")) {
			List<File> files = latex(mainFile, lang);
			try {
				FileUtil.copyFiles(files, mainFile.getCanonicalFile().getParentFile());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else if (cmd.hasOption("pdf")) {
			List<File> files = latex(mainFile, lang);
			files = pdf(files, lang);
			try {
				FileUtil.copyFiles(files, mainFile.getCanonicalFile().getParentFile());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else if (cmd.hasOption("xml")) {
			xml(mainFile, lang);
		} else if (cmd.hasOption("html")) {
			html(mainFile, lang);
		} else if (cmd.hasOption("unparse")) {
			unparse(mainFile, lang);
		} else {
			// default option: if (cmd.hasOption("compile"))
			compile(mainFile, lang, step);
		}
		if (GlobalSettings.verbose)
			sw.printTotal("Total");
		GlobalSettings.kem.print();
	}

	private static void lint(File mainFile, String mainModule) {
		try {
			File canonicalFile = mainFile.getCanonicalFile();
			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(canonicalFile, mainModule);

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

	private static List<File> pdf(List<File> files, String lang) {
		File latexFile = files.get(0);
		files.clear();

		try {
			Stopwatch sw = new Stopwatch();
			// Run pdflatex.
			String pdfLatex = "pdflatex";
			String argument = latexFile.getCanonicalPath();
			// System.out.println(argument);

			ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument, "-interaction", "nonstopmode");
			pb.directory(latexFile.getParentFile());

			pb.redirectErrorStream(true);
			try {
				Process process = pb.start();
				InputStream is = process.getInputStream();
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				while (br.readLine() != null) {
				}
				process.waitFor();
				if (process.exitValue() != 0) {
					KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1003, "", "");
					GlobalSettings.kem.register(exception);
				}
				process = pb.start();
				is = process.getInputStream();
				isr = new InputStreamReader(is);
				br = new BufferedReader(isr);
				while (br.readLine() != null) {
				}
				process.waitFor();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latex2PDF");
			}

			files.add(new File(FileUtil.stripExtension(latexFile.getCanonicalPath()) + ".pdf"));
		} catch (IOException e) {
			KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1001, "", "");
			GlobalSettings.kem.register(exception);
		}

		return files;
	}

	public static void pdfClean(String[] extensions) {
		for (int i = 0; i < extensions.length; i++)
			new File(GlobalSettings.mainFileWithNoExtension + extensions[i]).delete();
	}

	public static List<File> latex(File mainFile, String mainModule) {
		List<File> result = new ArrayList<File>();
		try {

			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			String fileSep = System.getProperty("file.separator");

			GlobalSettings.literate = true;
			// compile a definition here

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.loadDefinition(mainFile, mainModule);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Total parsing");
			}

			LatexFilter lf = new LatexFilter();
			javaDef.accept(lf);

			String endl = System.getProperty("line.separator");

			String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k.sty";
			String dotKLatexStyle = DefinitionHelper.dotk.getAbsolutePath() + fileSep + "k.sty";

			FileUtil.saveInFile(dotKLatexStyle, FileUtil.getFileContent(kLatexStyle));

			String latexified = "\\nonstopmode" + endl + "\\documentclass{article}" + endl + "\\usepackage[" + GlobalSettings.style + "]{k}" + endl;
			String preamble = lf.getPreamble().toString();
			latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

			String latexifiedFile = DefinitionHelper.dotk.getAbsolutePath() + fileSep + FileUtil.stripExtension(canonicalFile.getName()) + ".tex";
			result.add(new File(latexifiedFile));
			result.add(new File(dotKLatexStyle));
			FileUtil.saveInFile(latexifiedFile, latexified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latex Generation");
			}

		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}

		return result;
	}

	private static String html(File mainFile, String lang) {
		org.kframework.kil.Definition javaDef;
		try {
			GlobalSettings.literate = true;

			String fileSep = System.getProperty("file.separator");
			String htmlIncludePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;

			javaDef = org.kframework.utils.DefinitionLoader.loadDefinition(mainFile, lang);
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			Stopwatch sw = new Stopwatch();
			HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath);
			javaDef.accept(htmlFilter);

			String html = htmlFilter.getHTML();

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.html", html);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".html", html);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Html Generation");
			}

			return html;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	private static String unparse(File mainFile, String lang) {
		org.kframework.kil.Definition javaDef;
		try {
			GlobalSettings.literate = true;

			javaDef = org.kframework.utils.DefinitionLoader.loadDefinition(mainFile, lang);
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			Stopwatch sw = new Stopwatch();
			UnparserFilter unparserFilter = new UnparserFilter();
			javaDef.accept(unparserFilter);

			String unparsedText = unparserFilter.getResult();

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.k", unparsedText);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".unparsed.k", unparsedText);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Unparsing");
			}

			return unparsedText;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static String xml(File mainFile, String mainModule) {
		try {
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			// compile a definition here

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(canonicalFile, mainModule);

			Stopwatch sw = new Stopwatch();
			javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddEmptyLists());

			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(javaDef);

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.xml", xml);

			FileUtil.saveInFile(canonicalFile.getAbsolutePath().replaceFirst("\\.k$", "") + ".xml", xml);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("XML Generation");
			}

			return xml;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	private static void fromxml(File xmlFile, String lang, String step) {
		try {
			// initial setup
			File canoFile = xmlFile.getCanonicalFile();

			// unmarshalling
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			org.kframework.kil.Definition javaDef = (org.kframework.kil.Definition) xstream.fromXML(canoFile);
			// This is essential for generating maude
			javaDef.preprocess();

			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());
			// javaDef.accept(new CollectSubsortsVisitor());
			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());

			compile(javaDef, step);

		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static String maudify(File mainFile, String mainModule) {
		try {
			// compile a definition here
			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(f, mainModule);

			Stopwatch sw = new Stopwatch();

			MaudeFilter maudeFilter = new MaudeFilter();
			javaDef.accept(maudeFilter);

			String maudified = maudeFilter.getResult();

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.maude", maudified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maude Generation");
			}

			return maudified;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static void compile(File mainFile, String mainModule, String step) {
		try {
			// TODO: trateaza erorile de compilare
			GlobalSettings.kem.print(KExceptionGroup.COMPILER);

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(f, mainModule);

			Stopwatch sw = new Stopwatch();

			MaudeFilter maudeFilter = new MaudeFilter();
			javaDef.accept(maudeFilter);
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.maude", maudeFilter.getResult());

			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(javaDef);

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/defx.xml", xml);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Save in file");
			}

			compile(javaDef, step);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void compile(org.kframework.kil.Definition javaDef, String step) {
		// init stopwatch
		Stopwatch sw = new Stopwatch();

		try {
			javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddEmptyLists());
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Empty Lists");
			}

			MaudeFilter maudeFilter1 = new MaudeFilter();
			javaDef.accept(maudeFilter1);
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/lists.maude", maudeFilter1.getResult());

			AutomaticModuleImportsTransformer amit = new AutomaticModuleImportsTransformer();
			try {
				javaDef = (org.kframework.kil.Definition) javaDef.accept(amit);
			} catch (TransformerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Automatic Module Imports");
			}

			DittoFilter df = new DittoFilter();
			javaDef.accept(df);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Ditto Filter");
			}

			javaDef = new FlattenModules().compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Flatten Modules");
			}

			javaDef = new CompilerTransformerStep(new DesugarStreams()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Desugar  Streams");
			}

			javaDef = new CompilerTransformerStep(new ResolveFunctions()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Functions");
			}

			javaDef = new CompilerTransformerStep(new AddKCell()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add K Cell");
			}

			javaDef = new CompilerTransformerStep(new ResolveFresh()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Fresh");
			}

			if (GlobalSettings.addTopCell) {
				javaDef = new CompilerTransformerStep(new AddTopCell()).compile(javaDef);
				if (GlobalSettings.verbose) {
					sw.printIntermediate("Add Top Cell");
				}
			}

			javaDef = new AddEval().compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Eval");
			}

			javaDef = new CompilerTransformerStep(new ResolveBinder()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Binder");
			}

			javaDef = new CompilerTransformerStep(new ResolveAnonymousVariables()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Anonymous Variables");
			}

			javaDef = new CompilerTransformerStep(new ResolveBlockingInput()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Blocking Input");
			}

			javaDef = new CompilerTransformerStep(new GenerateSyntaxPredicates()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Generate Syntax Predicates");
			}

			javaDef = new CompilerTransformerStep(new GenerateSymbolicSyntaxPredicates()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Generate Symbolic Syntax Predicates");
			}

			javaDef = new CompilerTransformerStep(new ResolveSyntaxPredicates()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Syntax Predicates");
			}

			javaDef = new CompilerTransformerStep(new ResolveBuiltins()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Builtins");
			}

			javaDef = new CompilerTransformerStep(new ResolveListOfK()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve ListOfK");
			}

			javaDef = new CompilerTransformerStep(new FlattenSyntax()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Flatten Syntax");
			}

			javaDef = new CompilerTransformerStep(new ResolveHybrid()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Hybrid");
			}

			ConfigurationStructureVisitor cfgStrVisitor = new ConfigurationStructureVisitor();
			javaDef.accept(cfgStrVisitor);
			int cfgMaxLevel = cfgStrVisitor.getMaxLevel();
			Map<String, ConfigurationStructure> cfgStr = cfgStrVisitor.getConfig();

			javaDef = new CompilerTransformerStep(new ResolveContextAbstraction(cfgMaxLevel, cfgStr)).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Context Abstraction");
			}

			javaDef = new CompilerTransformerStep(new ResolveDefaultTerms(cfgStr)).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Default Terms");
			}

			javaDef = new CompilerTransformerStep(new ResolveOpenCells()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Open Cells");
			}

			String load = "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/k-prelude\"\n";
			// load += "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/pl-builtins\"\n";

			// load libraries if any
			String maudeLib = GlobalSettings.lib.equals("") ? "" : "load " + KPaths.windowfyPath(new File(GlobalSettings.lib).getAbsolutePath()) + "\n";
			load += maudeLib;

			String transition = metadataTags(GlobalSettings.transition);
			String superheat = metadataTags(GlobalSettings.superheat);
			String supercool = metadataTags(GlobalSettings.supercool);

			javaDef = (Definition) javaDef.accept(new AddStrictStar());

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Strict Star");
			}

			javaDef = (Definition) javaDef.accept(new AddDefaultComputational());

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Default Computational");
			}

			javaDef = (Definition) javaDef.accept(new AddOptionalTags());

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Optional Tags");
			}

			MaudeFilter maudeFilter = new MaudeFilter();
			javaDef.accept(maudeFilter);

			String compile = load + maudeFilter.getResult() + " load \"" + KPaths.getKBase(true) + "/bin/maude/compiler/all-tools\"\n" + "---(\n" + "rew in COMPILE-ONESHOT : partialCompile('"
					+ javaDef.getMainModule() + ", '" + step + ") .\n" + "quit\n" + "---)\n" + " loop compile .\n" + "(compile " + javaDef.getMainModule() + " " + step + " transitions " + transition
					+ " superheats " + superheat + " supercools " + supercool + " anywheres \"anywhere=() function=() predicate=() macro=()\" "
					+ "defineds \"function=() predicate=() defined=()\" .)\n" + "quit\n";

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/compile.maude", compile);

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate Maude file");

			// call maude to kompile the definition
			String compiled = MaudeRun.run_maude(DefinitionHelper.dotk.getAbsoluteFile(), compile);

			int start = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-BEGIN---") + "---K-MAUDE-GENERATED-OUTPUT-BEGIN---".length();
			int enddd = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-END-----");
			compiled = compiled.substring(start, enddd);

			String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$", "");
			FileUtil.saveInFile(defFile + "-compiled.maude", load + compiled);

			if (GlobalSettings.verbose)
				sw.printIntermediate("RunMaude");
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static List<String> metadataParse(String tags) {
		String[] alltags = tags.split("\\s+");
		List<String> result = new ArrayList<String>();
		for (int i = 0; i < alltags.length; i++)
			result.add(alltags[i]);
		return result;
	}

	private static String metadataTags(List<String> tags) {
		String result = "";
		for (String s : tags) {
			result += s + "=()";
		}
		return "\"" + result + "\"";
	}
}
