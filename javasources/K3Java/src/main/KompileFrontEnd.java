package main;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import k.utils.FileUtil;
import k.utils.KPaths;
import k.utils.MaudeRun;
import k.utils.ResourceExtractor;
import k.utils.Sdf2Table;
import k.utils.Stopwatch;
import k.utils.XmlLoader;
import k3.basic.Definition;
import k3.loader.AddConsesVisitor;
import k3.loader.BasicParser;
import k3.loader.ProgramSDF;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.disambiguate.AmbFilter;
import ro.uaic.info.fmse.disambiguate.BestFitFilter;
import ro.uaic.info.fmse.disambiguate.FlattenListsFilter;
import ro.uaic.info.fmse.disambiguate.GetFitnessUnitFileCheckVisitor;
import ro.uaic.info.fmse.disambiguate.GetFitnessUnitKCheckVisitor;
import ro.uaic.info.fmse.disambiguate.GetFitnessUnitTypeCheckVisitor;
import ro.uaic.info.fmse.disambiguate.TypeInferenceSupremumFilter;
import ro.uaic.info.fmse.disambiguate.TypeSystemFilter;
import ro.uaic.info.fmse.disambiguate.VariableTypeInferenceFilter;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.errorsystem.KMessages;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.html.HTMLFilter;
import ro.uaic.info.fmse.latex.LatexFilter;
import ro.uaic.info.fmse.lists.EmptyListsVisitor;
import ro.uaic.info.fmse.loader.CollectConsesVisitor;
import ro.uaic.info.fmse.loader.CollectSubsortsVisitor;
import ro.uaic.info.fmse.loader.UpdateReferencesVisitor;
import ro.uaic.info.fmse.pp.Preprocessor;

import com.thoughtworks.xstream.XStream;

public class KompileFrontEnd {
	public static void kompile(String[] args) {
		Stopwatch sw = new Stopwatch();
		KompileOptionsParser op = new KompileOptionsParser();

		CommandLine cmd = op.parse(args);

		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		}

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		if (cmd.hasOption("nofilename")) {
			GlobalSettings.noFilename = true;
		}

		// TODO: temporary to test the java disambiguator
		if (cmd.hasOption("tempDisamb"))
			GlobalSettings.tempDisamb = true;

		if (cmd.hasOption("warnings"))
			GlobalSettings.warnings = true;

		// set lib if any
		if (cmd.hasOption("lib")) {
			GlobalSettings.lib = cmd.getOptionValue("lib");
		}
		if (cmd.hasOption("syntax-module"))
			GlobalSettings.synModule = cmd.getOptionValue("syntax-module");

		if (cmd.hasOption("fromxml")) {
			File xmlFile = new File(cmd.getOptionValue("fromxml"));
			if (cmd.hasOption("lang"))
				fromxml(xmlFile, cmd.getOptionValue("lang"));
			else
				fromxml(xmlFile, xmlFile.getName().replaceFirst("\\.[a-zA-Z]+$", "").toUpperCase());
			System.exit(0);
		}

		String def = null;
		if (cmd.hasOption("def"))
			def = cmd.getOptionValue("def");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "You have to provide a file in order to compile!.", "command line", "System file.", 0));
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
		} else {
			// default option: if (cmd.hasOption("compile"))
			compile(mainFile, lang, maudify(mainFile, lang));
		}
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		GlobalSettings.kem.print(GlobalSettings.level);
	}

	private static void pdf(File mainFile, String lang) {
		latex(mainFile, lang);

		try {
			// Run pdflatex.
			String pdfLatex = "pdflatex";
			String argument = GlobalSettings.mainFileWithNoExtension + ".tex";
			System.out.println(argument);

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
					KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1003, "", "", 0);
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
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			// // Apparently I have to do this for now. I'll search for a better solution soon.
			// InputStream is = process.getInputStream();
			// InputStreamReader isr = new InputStreamReader(is);
			// BufferedReader br = new BufferedReader(isr);
			// // String line;
			// while (br.readLine() != null) {
			// }
			// ;
			// / while((line = br.readLine()) != null){System.out.println(line);}

		} catch (IOException e) {
			KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1001, "", "", 0);
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

			GlobalSettings.latex = true;
			// compile a definition here

			ro.uaic.info.fmse.k.Definition javaDef = k.utils.DefinitionLoader.loadDefinition(mainFile, mainModule, GlobalSettings.verbose);

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
				sw.printIntermediate("Latexif         = ");
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
		ro.uaic.info.fmse.k.Definition javaDef;
		try {
			javaDef = k.utils.DefinitionLoader.loadDefinition(mainFile, lang, GlobalSettings.verbose);
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();

			Stopwatch sw = new Stopwatch();
			HTMLFilter htmlFilter = new HTMLFilter();
			javaDef.accept(htmlFilter);

			String html = htmlFilter.getResult();

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

	public static String xml(File mainFile, String mainModule) {
		try {
			// for now just use this file as main argument
			File canonicalFile = mainFile.getCanonicalFile();

			File dotk = new File(canonicalFile.getParent() + "/.k");
			dotk.mkdirs();

			// compile a definition here

			ro.uaic.info.fmse.k.Definition javaDef = k.utils.DefinitionLoader.parseDefinition(mainModule, canonicalFile, dotk, GlobalSettings.verbose);

			Stopwatch sw = new Stopwatch();
			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());

			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(javaDef);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.xml", xml);

			FileUtil.saveInFile(canonicalFile.getAbsolutePath().replaceFirst("\\.k$", "") + ".xml", xml);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latexif         = ");
			}

			return xml;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	private static void fromxml(File xmlFile, String lang) {
		try {
			// initial setup
			File canoFile = xmlFile.getCanonicalFile();
			File dotk = new File(canoFile.getParent() + "/.k");
			dotk.mkdirs();

			// unmarshalling
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			ro.uaic.info.fmse.k.Definition javaDef = (ro.uaic.info.fmse.k.Definition) xstream.fromXML(canoFile);
			// This is essential for generating maude
			javaDef.preprocess();

			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());
			// javaDef.accept(new CollectSubsortsVisitor());
			// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());

			Stopwatch sw = new Stopwatch();

			// save it
			String maudified = javaDef.toMaude();
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.maude", maudified);
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify         = ");
			}

			compile(canoFile, lang, maudified);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static String maudify(File mainFile, String mainModule) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

			// ------------------------------------- basic parsing
			Definition def = new Definition();
			def.slurp(f, true);
			def.setMainFile(mainFile);
			def.setMainModule(mainModule);
			def.addConsToProductions();

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
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm/Program.sdf", def.getSDFForPrograms());

			String newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/pgm/Program.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Pgm    = ");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/pgm"), "Program");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLPgm = ");

			// generate a copy for the definition and modify it to generate the intermediate data
			Definition def2 = def.clone();// (Definition) Cloner.copy(def);
			def2.makeConsLists();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.sbs", def2.getSubsortingAsStrategoTerms());
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cons", def2.getConsAsStrategoTerms());

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			oldSdf = "";
			if (new File(dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def/Integration.sdf", def2.getSDFForDefinition());
			newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Def    = ");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/def"), "K3Disamb");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLDef = ");

			// ------------------------------------- import files in Stratego
			k3parser.KParser.ImportSbs(dotk.getAbsolutePath() + "/Integration.sbs");
			k3parser.KParser.ImportCons(dotk.getAbsolutePath() + "/Integration.cons");
			k3parser.KParser.ImportTbl(dotk.getAbsolutePath() + "/def/K3Disamb.tbl");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			// ------------------------------------- parse configs
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cells", def.getCellsFromConfigAsStrategoTerm());
			k3parser.KParser.ImportCells(dotk.getAbsolutePath() + "/Integration.cells");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Configs = ");

			// ----------------------------------- parse rules
			def.parseRules();

			// ----------------------------------- preprocessiong steps
			Preprocessor preprocessor = new Preprocessor();
			Document preprocessedDef = preprocessor.run(def.getDefAsXML());

			XmlLoader.writeXmlFile(preprocessedDef, dotk.getAbsolutePath() + "/def.xml");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Rules   = ");

			ro.uaic.info.fmse.k.Definition javaDef = new ro.uaic.info.fmse.k.Definition((Element) preprocessedDef.getFirstChild());

			javaDef.accept(new UpdateReferencesVisitor());
			javaDef.accept(new CollectConsesVisitor());
			javaDef.accept(new CollectSubsortsVisitor());

			// disambiguation steps

			if (!GlobalSettings.tempDisamb) {
				// javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new CorrectRewriteFilter());
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitFileCheckVisitor()));
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new TypeSystemFilter());
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new TypeInferenceSupremumFilter());
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new VariableTypeInferenceFilter());
				javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new FlattenListsFilter());
				if (GlobalSettings.verbose)
					sw.printIntermediate("Disambiguate    = ");
			}
			// last resort disambiguation
			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());

			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());

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
			ro.uaic.info.fmse.k.Definition def = new ro.uaic.info.fmse.k.Definition();
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
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.PARSER, "Could not find main syntax module used to generate a parser for programs: " + def.getMainSyntaxModule(), def.getMainFile(), "File system.", 0));
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

	public static void compile(File mainFile, String mainModule, String maudified) {
		try {
			// TODO: trateaza erorile de compilare
			GlobalSettings.kem.print(GlobalSettings.level, KExceptionGroup.COMPILER);

			// init stopwatch
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			File dotk = new File(f.getParent() + "/.k");

			String load = "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/k-prelude\"\n";
			// load += "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/pl-builtins\"\n";

			// load libraries if any
			String maudeLib = GlobalSettings.lib.equals("") ? "" : "load " + KPaths.windowfyPath(new File(GlobalSettings.lib).getAbsolutePath()) + "\n";
			load += maudeLib;

			String compile = load + maudified + " load \"" + KPaths.getKBase(true) + "/bin/maude/compiler/all-tools\"\n loop compile .\n(compile " + mainModule
					+ " transitions \"transition=()\" superheats \"superheat=()\" supercools \"supercool=()\" anywheres \"anywhere=() function=() predicate=()\" defineds \"function=() predicate=() defined=()\" .)\n quit\n";

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/compile.maude", compile);

			// call maude to kompile the definition
			String compiled = MaudeRun.run_maude(dotk.getAbsoluteFile(), compile);

			int start = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-BEGIN---") + "---K-MAUDE-GENERATED-OUTPUT-BEGIN---".length();
			int enddd = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-END-----");
			compiled = compiled.substring(start, enddd);

			String defFile = mainFile.getName().replaceFirst("\\.[a-zA-Z]+$", "");
			FileUtil.saveInFile(dotk.getParent() + "/" + defFile + "-compiled.maude", load + compiled);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("RunMaude        = ");
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
