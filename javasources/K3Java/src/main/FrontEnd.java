package main;

import java.io.*;
import k.utils.*;
import k3.basic.Definition;
import org.w3c.dom.Document;
import ro.uaic.fmse.k2m.main.Kil2Maude;

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
			def.slurp(f);
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
				Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/def"), "K3");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLDef = ");

			// ------------------------------------- import files in Stratego
			k3parser.KParser.ImportSbs(dotk.getAbsolutePath() + "/Integration.sbs");
			k3parser.KParser.ImportDitto(dotk.getAbsolutePath() + "/Integration.ditto");
			k3parser.KParser.ImportCons(dotk.getAbsolutePath() + "/Integration.cons");
			k3parser.KParser.ImportTbl(dotk.getAbsolutePath() + "/def/K3.tbl");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			// ------------------------------------- parse configs
			FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cells", def.getCellsFromConfigAsStrategoTerm());
			k3parser.KParser.ImportCells(dotk.getAbsolutePath() + "/Integration.cells");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Configs = ");

			// ----------------------------------- parse rules
			def.parseRules();

			XmlLoader.writeXmlFile(def.getDefAsXML(), dotk.getAbsolutePath() + "/def.xml");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Rules   = ");

			String maudified = Kil2Maude.KILFiletoMEL(dotk.getAbsolutePath() + "/def.xml");

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

			String load = "load \"" + Kil2Maude.getKBase(true) + "/bin/maude/lib/k-prelude\"\n";

			String compile = load
					+ maudified
					+ " load \""
					+ Kil2Maude.getKBase(true)
					+ "/bin/maude/compiler/all-tools\"\n loop compile .\n(compile "
					+ mainModule
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

				XmlLoader.reportErrors(doc.getFirstChild());
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

			System.out.println(Kil2Maude.KILProgram2Ast(definition, program));
			String pgmMaude = Kil2Maude.KILProgram2Maude(definition, program, defFile);

			FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm.maude", pgmMaude);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify Program = ");
				sw.printTotal("Total           = ");
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
}
