package main;

import java.io.File;
import java.io.IOException;

import k.utils.FileUtil;
import k.utils.Stopwatch;
import k.utils.XmlLoader;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.transitions.labelify.KAppModifier;

public class KastFrontEnd {

	public static void kast(String[] args) {
		Stopwatch sw = new Stopwatch();
		KastOptionsParser op = new KastOptionsParser();
		CommandLine cmd = op.parse(args);
		// set verbose
		if (cmd.hasOption("verbose")) {
			GlobalSettings.verbose = true;
		}

		if (cmd.hasOption("nofilename")) {
			GlobalSettings.noFilename = true;
		}
		// options: help
		if (cmd.hasOption("help")) {
			k.utils.Error.helpExit(op.getHelp(), op.getOptions());
		}
		String pgm = null;
		if (cmd.hasOption("pgm"))
			pgm = cmd.getOptionValue("pgm");
		else {
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				k.utils.Error.report("You have to provide a file in order to kast a program!.");
			else
				pgm = restArgs[0];
		}

		File mainFile = new File(pgm);
		if (!mainFile.exists())
			k.utils.Error.report("Could not find file: " + pgm);

		File def = null;
		if (cmd.hasOption("def")) {
			def = new File(cmd.getOptionValue("def"));
			if (!def.exists())
				k.utils.Error.report("Could not find file: " + def);
		} else {
			// search for the definition
			try {
				File pgmFolder = mainFile.getCanonicalFile();
				boolean found = false;
				while (!found) {
					// check to see if I got to / or drive folder
					if (pgmFolder.getAbsoluteFile().getParentFile() == null)
						break;
					File dotk = new File(pgmFolder.getParent() + "/.k");
					pgmFolder = pgmFolder.getParentFile();
					if (dotk.exists()) {
						File defXml = new File(dotk.getCanonicalPath() + "/def.xml");
						if (!defXml.exists()) {
							k.utils.Error.report("Could not find the compiled definition in: " + dotk);
						}

						Document doc = XmlLoader.getXMLDoc(FileUtil.getFileContent(defXml.getAbsolutePath()));
						Element el = (Element) doc.getElementsByTagName("def").item(0);
						def = new File(el.getAttribute("mainFile"));
						found = true;
					}
				}

				if (def == null)
					k.utils.Error.report("Could not find a compiled definition, please provide one using the -def option");
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		parsePgm(mainFile, def);
		if (GlobalSettings.verbose)
			sw.printTotal("Total           = ");
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

			out = out.accept(new KAppModifier());
			String kast = out.toMaude();

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
