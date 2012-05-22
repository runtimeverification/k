package main;

import java.io.File;
import java.io.IOException;
import java.util.List;

import k.utils.FileUtil;
import k.utils.KPaths;
import k.utils.MaudeRun;
import k.utils.ResourceExtractor;
import k.utils.Sdf2Table;
import k.utils.Stopwatch;
import k.utils.XmlLoader;
import k3.basic.Definition;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.errorsystem.KException.Level;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.latex.LatexFilter;
import ro.uaic.info.fmse.lists.EmptyListsVisitor;
import ro.uaic.info.fmse.loader.AmbFilter;
import ro.uaic.info.fmse.loader.CollectSubsortsVisitor;
import ro.uaic.info.fmse.pp.Preprocessor;

public class KompileFrontEnd {

	public static void kompile(String[] args) {
		Stopwatch sw = new Stopwatch();
		KompileOptionsParser op = new KompileOptionsParser();

		CommandLine cmd = op.parse(args);

		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		if (cmd.hasOption("nofilename")) {
			GlobalSettings.noFilename = true;
		}

		// set lib if any
		if (cmd.hasOption("lib")) {
			GlobalSettings.lib = cmd.getOptionValue("lib");
		}
		if (cmd.hasOption("syntax-module"))
			GlobalSettings.synModule = cmd.getOptionValue("syntax-module");

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

		if (!mainFile.exists())
			k.utils.Error.report("Could not find file: " + file);

		if (cmd.hasOption("lang"))
			lang = cmd.getOptionValue("lang");
		else
			lang = mainFile.getName().substring(0, mainFile.getName().length() - 2).toUpperCase();

		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		} else if (cmd.hasOption("maudify")) {
			maudify(mainFile, lang);
		} else if (cmd.hasOption("latex")) {
			latex(mainFile, lang);
		} else if (cmd.hasOption("pdf")) {
			pdf(mainFile, lang);
		} else {
			// default option: if (cmd.hasOption("compile"))
			compile(mainFile, lang);
		}
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
		List<Level> levels = null;
		GlobalSettings.kem.print(levels);
	}

	private static void pdf(File mainFile, String lang) {
		latex(mainFile, lang);
		
//		try {
//			// Run pdflatex.
//			String pdfLatex = "pdflatex";
//			String fileSep = System.getProperty("file.separator");
//			File f = mainFile.getCanonicalFile();
//			String argument = "";
//			System.out.println(argument);
//			
//			ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument);
//			Process process;
//
//			process = pb.start();
//			process.wait();
//			if (process.exitValue() == 0)
//				System.out.println("Ok.");
//			else System.out.println("Not ok");
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (InterruptedException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
	}

	public static String latex(File mainFile, String mainModule) {
		try {
			GlobalSettings.latex = true;
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();

			File dotk = new File(f.getParent() + "/.k");
			dotk.mkdirs();

			// ------------------------------------- basic parsing
			Definition def = new Definition();
			def.slurp(f, true);
			def.setMainModule(mainModule);
			def.setMainFile(mainFile);
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
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.ditto", def2.getDittosAsStrategoTerm());

			def2.replaceDittoCons();

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
			k3parser.KParser.ImportDitto(dotk.getAbsolutePath() + "/Integration.ditto");
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

			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());
			javaDef.accept(new CollectSubsortsVisitor());
			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new EmptyListsVisitor());

			LatexFilter lf = new LatexFilter();
			javaDef.accept(lf);
			
			String endl = System.getProperty("line.separator");
			String fileSep = System.getProperty("file.separator");
			String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k";
			
			String latexified = "\\documentclass{article}" + endl
			+ "\\usepackage[poster,style=bubble]{" + kLatexStyle + "}" + endl
//			+ "\\setlength{\\parindent}{1em}" + endl
			+ "\\title{" + mainModule + "}" + endl
//			+ "\\author{Grigore Ro\\c{s}u (\\texttt{grosu@illinois.edu})}" + endl
//			+ "\\organization{University of Illinois at Urbana-Champaign}" + endl
			+ "\\begin{document}" + endl
			+ lf.getResult()
			+ "\\end{document}" + endl;
			
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.tex", latexified);

			FileUtil.saveInFile(f.getAbsolutePath().replaceFirst("\\.k$", "") + ".tex", latexified);
			
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
			def.setMainModule(mainModule);
			def.setMainFile(mainFile);
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
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.ditto", def2.getDittosAsStrategoTerm());

			def2.replaceDittoCons();

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
			k3parser.KParser.ImportDitto(dotk.getAbsolutePath() + "/Integration.ditto");
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

			javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());
			javaDef.accept(new CollectSubsortsVisitor());
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

	public static void compile(File mainFile, String mainModule) {
		try {
			String maudified = maudify(mainFile, mainModule);
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

			String defFile = mainFile.getName().substring(0, mainFile.getName().length() - 2);
			FileUtil.saveInFile(dotk.getParent() + "/" + defFile + "-compiled.maude", load + compiled);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("RunMaude        = ");
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
