package org.kframework.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.kframework.backend.html.HTMLFilter;
import org.kframework.backend.latex.LatexFilter;
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
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveBinder;
import org.kframework.compile.transformers.ResolveBlockingInput;
import org.kframework.compile.transformers.ResolveFresh;
import org.kframework.compile.transformers.ResolveHybrid;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveSyntaxPredicates;
import org.kframework.compile.utils.CompilerTransformerStep;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kompile.lint.InfiniteRewrite;
import org.kframework.kompile.lint.KlintRule;
import org.kframework.kompile.lint.UnusedName;
import org.kframework.kompile.lint.UnusedSyntax;
import org.kframework.parser.generator.loader.AddConsesVisitor;
import org.kframework.parser.generator.loader.BasicParser;
import org.kframework.parser.generator.loader.ProgramSDF;
import org.kframework.utils.ResourceExtractor;
import org.kframework.utils.Sdf2Table;
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
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "File: " + errorFile.getName() + "(.k) not found.", errorFile.getAbsolutePath(), "File system."));
		}

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
		} else if (cmd.hasOption("tempc")) {
			tempc(mainFile, lang);
		} else if (cmd.hasOption("latex")) {
			latex(mainFile, lang);
		} else if (cmd.hasOption("pdf")) {
			pdf(mainFile, lang);
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
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print();
	}

	private static void lint(File mainFile, String mainModule) {
		try {
			File canonicalFile = mainFile.getCanonicalFile();
			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();
			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(mainModule, canonicalFile, dotk);

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

	private static void pdf(File mainFile, String lang) {
		latex(mainFile, lang);

		try {
			// Run pdflatex.
			String pdfLatex = "pdflatex";
			String argument = GlobalSettings.mainFileWithNoExtension + ".tex";
			// System.out.println(argument);

			ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument, "-interaction", "nonstopmode");

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
				pdfClean(new String[] { ".tex", ".aux", ".log", ".mrk", ".out", ".sty" });
				new File("k.sty").delete();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

		} catch (IOException e) {
			KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1001, "", "");
			GlobalSettings.kem.register(exception);
		}
		pdfClean(new String[] { ".aux", ".log", ".mrk", ".out" });
	}

	private static void pdfClean(String[] extensions) {
		for (int i = 0; i < extensions.length; i++)
			new File(GlobalSettings.mainFileWithNoExtension + extensions[i]).delete();
	}

	public static String latex(File mainFile, String mainModule) {
		try {
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			String fileSep = System.getProperty("file.separator");
			File dotk = new File(canonicalFile.getParent() + fileSep + ".k");
			dotk.mkdirs();

			GlobalSettings.literate = true;
			// compile a definition here

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.loadDefinition(mainFile, mainModule);

			Stopwatch sw = new Stopwatch();
			LatexFilter lf = new LatexFilter();
			javaDef.accept(lf);

			String endl = System.getProperty("line.separator");
			String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k.sty";
			FileUtil.saveInFile(canonicalFile.getParent() + fileSep + "k.sty", FileUtil.getFileContent(kLatexStyle));

			String latexified = "\\nonstopmode" + endl + "\\documentclass{article}" + endl + "\\usepackage[poster,style=bubble]{k}" + endl;
			String preamble = lf.getPreamble();
			latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.tex", latexified);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".tex", latexified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latexify        = ");
			}

			return latexified;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
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

			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();

			Stopwatch sw = new Stopwatch();
			HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath);
			javaDef.accept(htmlFilter);

			String html = htmlFilter.getHTML();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.html", html);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".html", html);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latexif         = ");
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

			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();

			Stopwatch sw = new Stopwatch();
			UnparserFilter unparserFilter = new UnparserFilter();
			javaDef.accept(unparserFilter);

			String unparsedText = unparserFilter.getResult();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.k", unparsedText);

			FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".unparsed.k", unparsedText);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Unparsing       = ");
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

			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();

			// compile a definition here

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(mainModule, canonicalFile, dotk);

			Stopwatch sw = new Stopwatch();
			javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddEmptyLists());

			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(javaDef);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.xml", xml);

			FileUtil.saveInFile(canonicalFile.getAbsolutePath().replaceFirst("\\.k$", "") + ".xml", xml);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Xmlify         = ");
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
			File dotk = new File(canoFile.getParent() + "/.k");
			dotk.mkdirs();

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

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(mainModule, f, dotk);

			Stopwatch sw = new Stopwatch();

			String maudified = javaDef.toMaude();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.maude", maudified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify         = ");
			}

			return maudified;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	/**
	 * TODO: make this the new basic parsing step. 1. slurp 2. gen files 3. gen TBLs 4. import files in stratego 5. parse configs 6. parse rules 7. ???
	 * 
	 * @param mainFile
	 * @param mainModule
	 * @return
	 */
	public static String tempc(File mainFile, String mainModule) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

			// ------------------------------------- basic parsing

			BasicParser bparser = new BasicParser();
			bparser.slurp(mainFile.getPath());

			// transfer information from the BasicParser object, to the Definition object
			org.kframework.kil.Definition def = new org.kframework.kil.Definition();
			def.setMainFile(mainFile.getCanonicalPath());
			def.setMainModule(mainModule);
			def.setModulesMap(bparser.getModulesMap());
			def.setItems(bparser.getModuleItems());

			if (GlobalSettings.synModule == null)
				def.setMainSyntaxModule(mainModule + "-SYNTAX");
			else
				def.setMainSyntaxModule(GlobalSettings.synModule);

			def.accept(new UpdateReferencesVisitor());
			def.accept(new CollectConsesVisitor());
			def.accept(new CollectSubsortsVisitor());
			def.accept(new CollectConfigCellsVisitor());
			def.accept(new AddConsesVisitor());

			if (GlobalSettings.verbose)
				sw.printIntermediate("Basic Parsing   = ");

			// ------------------------------------- generate files
			ResourceExtractor.ExtractAllSDF(dotk);

			ResourceExtractor.ExtractProgramSDF(dotk);

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			String oldSdf = "";
			if (new File(dotk.getAbsolutePath() + "/pgm/Program.sdf").exists())
				oldSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/pgm/Program.sdf");

			// make a set of all the syntax modules
			if (def.getModulesMap().get(def.getMainSyntaxModule()) == null) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.PARSER, "Could not find main syntax module used to generate a parser for programs: " + def.getMainSyntaxModule(), def.getMainFile(), "File system."));
			} else {
				FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm/Program.sdf", ProgramSDF.getSdfForPrograms(def));
			}

			String newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/pgm/Program.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Pgm    = ");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/pgm"), "Program");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLPgm = ");

			// generate a copy for the definition and modify it to generate the intermediate data
			// Definition def2 = def.clone();// (Definition) Cloner.copy(def);
			// def2.makeConsLists();
			//
			// FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.sbs", def2.getSubsortingAsStrategoTerms());
			// FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cons", def2.getConsAsStrategoTerms());
			//

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			oldSdf = "";
			if (new File(dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");
			// FileUtil.saveInFile(dotk.getAbsolutePath() + "/def/Integration.sdf", def2.getSDFForDefinition());
			newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Def    = ");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/def"), "K3Disamb");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLDef = ");

			// ------------------------------------- import files in Stratego
			// k3parser.KParser.ImportSbs(dotk.getAbsolutePath() + "/Integration.sbs");
			// k3parser.KParser.ImportCons(dotk.getAbsolutePath() + "/Integration.cons");
			// k3parser.KParser.ImportTbl(dotk.getAbsolutePath() + "/def/K3Disamb.tbl");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			// ------------------------------------- parse configs
			// FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cells", def.getCellsFromConfigAsStrategoTerm());
			// k3parser.KParser.ImportCells(dotk.getAbsolutePath() + "/Integration.cells");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Configs = ");

			// ----------------------------------- parse rules
			// def.parseRules();

			// ----------------------------------- preprocessiong steps
			// Preprocessor preprocessor = new Preprocessor();
			// Document preprocessedDef = preprocessor.run(def.getDefAsXML());
			//
			// XmlLoader.writeXmlFile(preprocessedDef, dotk.getAbsolutePath() + "/def.xml");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Rules   = ");

			// ro.uaic.info.fmse.k.Definition javaDef = new ro.uaic.info.fmse.k.Definition((Element) preprocessedDef.getFirstChild());
			//
			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());
			// javaDef.accept(new CollectSubsortsVisitor());
			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());
			//
			// String maudified = javaDef.toMaude();
			//
			// FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.maude", maudified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify         = ");
			}

			// return maudified;
			return "";
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

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

			org.kframework.kil.Definition javaDef = org.kframework.utils.DefinitionLoader.parseDefinition(mainModule, f, dotk);

			compile(javaDef, step);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public static void compile(org.kframework.kil.Definition javaDef, String step) {
		// init stopwatch
		Stopwatch sw = new Stopwatch();

		try {

			AutomaticModuleImportsTransformer amit = new AutomaticModuleImportsTransformer();
			try {
				javaDef = (org.kframework.kil.Definition) javaDef.accept(amit);
			} catch (TransformerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Automatic Module Imports         = ");
			}


			DittoFilter df = new DittoFilter();
			javaDef.accept(df);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Ditto Filter                     = ");
			}

			
			
			javaDef = new FlattenModules().compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Flatten Modules                  = ");
			}
			
			javaDef = new CompilerTransformerStep(new DesugarStreams()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Desugar  Streams                 = ");
			}

			javaDef = new CompilerTransformerStep(new AddKCell()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Desugar  Streams                 = ");
			}

			javaDef = new CompilerTransformerStep(new ResolveFresh()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Fresh                    = ");
			}

			if (GlobalSettings.addTopCell) {
				javaDef = new CompilerTransformerStep(new AddTopCell()).compile(javaDef);
				if (GlobalSettings.verbose) {
					sw.printIntermediate("Add Top Cell                     = ");
				}
			}

			javaDef = new AddEval().compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Eval                         = ");
			}

			javaDef = new CompilerTransformerStep(new ResolveBinder()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Binder                   = ");
			}

			javaDef = new CompilerTransformerStep(new ResolveAnonymousVariables()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Anonymous Variables      = ");
			}

			javaDef = new CompilerTransformerStep(new ResolveBlockingInput()).compile(javaDef);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Blocking Input           = ");
			}
						
			javaDef = new CompilerTransformerStep(new GenerateSyntaxPredicates()).compile(javaDef);
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Generate Syntax Predicates       = ");
			}
			
			javaDef = new CompilerTransformerStep(new ResolveSyntaxPredicates()).compile(javaDef);
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Syntax Predicates        = ");
			}
			
			javaDef = new CompilerTransformerStep(new ResolveListOfK()).compile(javaDef);		
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve ListOfK                  = ");
			}
			
			javaDef = new CompilerTransformerStep(new FlattenSyntax()).compile(javaDef);
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Flatten Syntax                   = ");
			}
			
			javaDef = new CompilerTransformerStep(new ResolveHybrid()).compile(javaDef);		

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Resolve Hybrid                   = ");
			}
			
			File f = new File(javaDef.getMainFile()).getCanonicalFile();

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

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
				sw.printIntermediate("Add Strict Star                  = ");
			}
			
			javaDef = (Definition) javaDef.accept(new AddDefaultComputational());
			
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Default Computational        = ");
			}
			
			javaDef = (Definition) javaDef.accept(new AddOptionalTags());

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Add Optional Tags                = ");
			}

			String compile = load 
					+ javaDef.toMaude() 
					+ " load \"" + KPaths.getKBase(true) + "/bin/maude/compiler/all-tools\"\n"
					+ "---(\n"
					+ "red in COMPILE-ONESHOT : partialCompile('" + javaDef.getMainModule() + ", '" + step + ") .\n"
					+ "quit\n"
					+ "---)\n"
					+ " loop compile .\n" + 
					"(compile " + javaDef.getMainModule() + " " + step 
					+ " transitions " + transition + " superheats " + superheat + " supercools " + supercool 
					+ " anywheres \"anywhere=() function=() predicate=() macro=()\" " 
					+  "defineds \"function=() predicate=() defined=()\" .)\n" 
					+ "quit\n";

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/compile.maude", compile);

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate Maude file              = ");

			// call maude to kompile the definition
			String compiled = MaudeRun.run_maude(dotk.getAbsoluteFile(), compile);

			int start = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-BEGIN---") + "---K-MAUDE-GENERATED-OUTPUT-BEGIN---".length();
			int enddd = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-END-----");
			compiled = compiled.substring(start, enddd);

			String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$", "");
			FileUtil.saveInFile(defFile + "-compiled.maude", load + compiled);

			if (GlobalSettings.verbose)
				sw.printIntermediate("RunMaude                         = ");
		} catch (IOException e) {
			e.printStackTrace();
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
