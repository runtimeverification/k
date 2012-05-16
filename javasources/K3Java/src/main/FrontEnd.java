package main;

import java.io.File;
import java.io.IOException;

import k.utils.FileUtil;
import k.utils.GlobalSettings;
import k.utils.KPaths;
import k.utils.MaudeRun;
import k.utils.ResourceExtractor;
import k.utils.Sdf2Table;
import k.utils.Stopwatch;
import k.utils.XmlLoader;
import k3.basic.Definition;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.lists.EmptyListsVisitor;
import ro.uaic.info.fmse.loader.AmbFilter;
import ro.uaic.info.fmse.loader.CollectSubsortsVisitor;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.pp.Preprocessor;
import ro.uaic.info.fmse.transitions.labelify.KAppFactory;

public class FrontEnd {

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

			new AmbFilter().visit(javaDef);
			new CollectSubsortsVisitor().visit(javaDef);
			new EmptyListsVisitor().visit(javaDef);

			String maudified = javaDef.toMaude();

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/def.maude", maudified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify         = ");
				sw.printTotal("Total           = ");
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
			Stopwatch sw = new Stopwatch();

			String maudified = maudify(mainFile, mainModule);

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

	public static void parsePgm(File mainFile, File defFile) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();
			File dotk = new File(defFile.getCanonicalFile().getParent() + "/.k");

			dotk.mkdirs();
			File tbl = new File(dotk.getCanonicalPath() + "/pgm/Program.tbl");

			// ------------------------------------- import files in Stratego
			k3parser.KParser.ImportTblPgm(tbl.getAbsolutePath());
			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			try {
				String content = FileUtil.getFileContent(f.getAbsolutePath());

				String parsed = k3parser.KParser.ParseProgramString(content);
				Document doc = XmlLoader.getXMLDoc(parsed);

				XmlLoader.addFilename(doc.getFirstChild(), mainFile.getAbsolutePath());
				XmlLoader.reportErrors(doc);
				XmlLoader.writeXmlFile(doc, dotk.getAbsolutePath() + "/pgm.xml");
			} catch (Exception e) {
				e.printStackTrace();
				k.utils.Error.report("Cannot parse program: " + e.getLocalizedMessage());
			}

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Parsing Program = ");
			}

			String definition = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def.xml");
			String program = FileUtil.getFileContent(dotk.getAbsolutePath() + "/pgm.xml");

			Document doc = ro.uaic.info.fmse.utils.xml.XML.getDocument(definition);
			ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());

			Document doc2 = ro.uaic.info.fmse.utils.xml.XML.getDocument(program);
			out = JavaClassesFactory.getTerm((Element) doc2.getDocumentElement().getFirstChild().getNextSibling());

			ASTNode kapp = KAppFactory.getTerm(out);
			String kast = kapp.toMaude();

			System.out.println(kast);

			String ast;
			ast = "load ../" + defFile.getName().substring(0, defFile.getName().length() - 2) + "-compiled.maude\n";
			ast += "set show command off .\n erewrite #eval(__((_|->_((# \"$PGM\"(.List{K})) , (\n\n";
			ast += kast;
			ast += "\n\n))),(.).Map))  .\n quit\n";

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm.maude", ast);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify Program = ");
				sw.printTotal("Total           = ");
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
}
