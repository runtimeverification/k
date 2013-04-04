package org.kframework.utils;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import org.kframework.compile.checks.CheckListDecl;
import org.kframework.compile.checks.CheckListOfKDeprecation;
import org.kframework.compile.checks.CheckModulesAndFilesImportsDecl;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxDecl;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Term;
import org.kframework.kil.loader.AddAutoIncludedModulesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectModuleImportsVisitor;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.generator.BasicParser;
import org.kframework.parser.generator.Definition2SDF;
import org.kframework.parser.generator.DefinitionSDF;
import org.kframework.parser.generator.ParseConfigsFilter;
import org.kframework.parser.generator.ParseRulesFilter;
import org.kframework.parser.generator.ProgramSDF;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.thoughtworks.xstream.XStream;

public class DefinitionLoader {
	public static org.kframework.kil.Definition loadDefinition(File mainFile, String lang, boolean autoinclude) throws IOException, Exception {
		org.kframework.kil.Definition javaDef;
		File canoFile = mainFile.getCanonicalFile();

		String extension = FileUtil.getExtension(mainFile.getAbsolutePath());
		if (extension.equals(".xml") || extension.equals(".bin")) {
			// unmarshalling
			XStream xstream;
			if (extension.equals(".xml")) {
				xstream = new XStream();
				xstream.aliasPackage("k", "org.kframework.kil");
				javaDef = (org.kframework.kil.Definition) xstream.fromXML(canoFile);
			} else {
				javaDef = (org.kframework.kil.Definition) BinaryLoader.fromBinary(new FileInputStream(canoFile));
			}

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Load definition from XML");

			javaDef.preprocess();

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

		} else {
			javaDef = parseDefinition(mainFile, lang, autoinclude);

			BinaryLoader.toBinary(javaDef, new FileOutputStream(DefinitionHelper.dotk.getAbsolutePath() + "/defx.bin"));

			if (GlobalSettings.xml) {
				XStream xstream = new XStream();
				xstream.aliasPackage("k", "org.kframework.kil");
				xstream.toXML(javaDef, new FileOutputStream(DefinitionHelper.dotk.getAbsolutePath() + "/defx.xml"));
			}

			if (GlobalSettings.verbose) {
				Stopwatch.sw.printIntermediate("Serialize Definition to XML");
			}

		}
		return javaDef;
	}

	/**
	 * step. 1. slurp 2. gen files 3. gen TBLs 4. import files in stratego 5. parse configs 6. parse rules 7. ???
	 * 
	 * @param mainFile
	 * @param mainModule
	 * @return
	 */
	public static Definition parseDefinition(File mainFile, String mainModule, boolean autoinclude) {
		try {
			// for now just use this file as main argument
			// ------------------------------------- basic parsing

			BasicParser bparser = new BasicParser(autoinclude);
			bparser.slurp(mainFile.getPath());

			// transfer information from the BasicParser object, to the Definition object
			org.kframework.kil.Definition def = new org.kframework.kil.Definition();
			def.setMainFile(mainFile.getCanonicalPath());
			def.setMainModule(mainModule);
			def.setModulesMap(bparser.getModulesMap());
			def.setItems(bparser.getModuleItems());

			if (!GlobalSettings.documentation) {
				if (GlobalSettings.synModule == null) {
					String synModule = mainModule + "-SYNTAX";
					if (!def.getModulesMap().containsKey(synModule)) {
						synModule = mainModule;
						String msg = "Could not find main syntax module used to generate a parser for programs (X-SYNTAX). Using: '" + synModule + "' instead.";
						GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.PARSER, msg, def.getMainFile(), "File system."));
					}
					def.setMainSyntaxModule(synModule);
				} else
					def.setMainSyntaxModule(GlobalSettings.synModule);

				if (!def.getModulesMap().containsKey(mainModule)) {
					String msg = "Could not find main module '" + mainModule + "'. Use -l(ang) option to specify another.";
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, def.getMainFile(), "File system."));
				}
			}
			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Basic Parsing");

			new CheckVisitorStep<Definition>(new CheckListOfKDeprecation()).check(def);

			def.preprocess();

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

			new CheckVisitorStep<Definition>(new CheckSyntaxDecl()).check(def);
			new CheckVisitorStep<Definition>(new CheckListDecl()).check(def);
			new CheckVisitorStep<Definition>(new CheckSortTopUniqueness()).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Checks");

			// ------------------------------------- generate files
			ResourceExtractor.ExtractDefSDF(new File(DefinitionHelper.dotk + "/def"));
			ResourceExtractor.ExtractGroundSDF(new File(DefinitionHelper.dotk + "/ground"));

			ResourceExtractor.ExtractProgramSDF(new File(DefinitionHelper.dotk + "/pgm"));

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			if (!GlobalSettings.documentation) {
				String oldSdfPgm = "";
				if (new File(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf").exists())
					oldSdfPgm = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				String newSdfPgm = ProgramSDF.getSdfForPrograms(def);

				FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf", newSdfPgm);
				newSdfPgm = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("File Gen Pgm");

				if (!oldSdfPgm.equals(newSdfPgm) || !new File(DefinitionHelper.dotk.getAbsoluteFile() + "/pgm/Program.tbl").exists()) {
					Sdf2Table.run_sdf2table(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/pgm"), "Program");
					if (GlobalSettings.verbose)
						Stopwatch.sw.printIntermediate("Generate TBLPgm");
				}
			}

			def.accept(new AddAutoIncludedModulesVisitor());
			def.accept(new CheckModulesAndFilesImportsDecl());
			def.accept(new CollectModuleImportsVisitor());

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			String oldSdf = "";
			if (new File(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf", DefinitionSDF.getSdfForDefinition(def));
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def));
			String newSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("File Gen Def");

			if (!oldSdf.equals(newSdf) || !new File(DefinitionHelper.dotk.getAbsoluteFile() + "/def/Concrete.tbl").exists()
					|| !new File(DefinitionHelper.dotk.getAbsoluteFile() + "/ground/Concrete.tbl").exists()) {
				// Sdf2Table.run_sdf2table(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/def"), "Concrete");
				Thread t1 = Sdf2Table.run_sdf2table_parallel(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/def"), "Concrete");
				if (!GlobalSettings.documentation) {
					Thread t2 = Sdf2Table.run_sdf2table_parallel(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/ground"), "Concrete");
					t2.join();
				}
				t1.join();
				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("Generate TBLDef");
			}
			// ------------------------------------- import files in Stratego
			org.kframework.parser.concrete.KParser.ImportTbl(DefinitionHelper.dotk.getAbsolutePath() + "/def/Concrete.tbl");

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Importing Files");

			// ------------------------------------- parse configs
			def = (Definition) def.accept(new ParseConfigsFilter());
			def.accept(new CollectConfigCellsVisitor());

			// sort List in streaming cells
			new CheckVisitorStep<Definition>(new CheckStreams()).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Parsing Configs");

			// ----------------------------------- parse rules
			def = (Definition) def.accept(new ParseRulesFilter());

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Parsing Rules");

			return def;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static Term parseCmdString(String content, String sort, String filename) {
		if (!DefinitionHelper.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}
		String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);
		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(DefinitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);

		org.kframework.kil.ASTNode config = (Term) JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());

		try {
			// TODO: reject rewrites
			// TODO: reject variables
			config = config.accept(new SentenceVariablesFilter());
			config = config.accept(new CellEndLabelFilter());
			config = config.accept(new CellTypesFilter());
			// config = config.accept(new CorrectRewritePriorityFilter());
			config = config.accept(new CorrectKSeqFilter());
			// config = config.accept(new CheckBinaryPrecedenceFilter());
			// config = config.accept(new InclusionFilter(localModule));
			// config = config.accept(new VariableTypeInferenceFilter());
			config = config.accept(new AmbDuplicateFilter());
			config = config.accept(new TypeSystemFilter());
			config = config.accept(new PriorityFilter());
			config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
			config = config.accept(new TypeInferenceSupremumFilter());
			config = config.accept(new PreferAvoidFilter());
			config = config.accept(new FlattenListsFilter());
			// config = config.accept(new CorrectRewriteSortFilter());
			// last resort disambiguation
			config = config.accept(new AmbFilter());
		} catch (TransformerException e) {
			String msg = "Cannot parse command line argument: " + e.getMessage();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, config.getFilename(), config.getLocation()));
		}

		return (Term) config;
	}

	public static ASTNode parsePattern(String pattern, String filename) {
		if (!DefinitionHelper.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString("rule " + pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(DefinitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		XmlLoader.writeXmlFile(doc, DefinitionHelper.kompiled + "/pattern.xml");

		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		try {
			// TODO: don't allow rewrites
			config = config.accept(new SentenceVariablesFilter());
			config = config.accept(new CellEndLabelFilter());
			config = config.accept(new CellTypesFilter());
			config = config.accept(new CorrectRewritePriorityFilter());
			config = config.accept(new CorrectKSeqFilter());
			// config = config.accept(new CheckBinaryPrecedenceFilter());
			// config = config.accept(new InclusionFilter(localModule));
			config = config.accept(new VariableTypeInferenceFilter());
			config = config.accept(new AmbDuplicateFilter());
			config = config.accept(new TypeSystemFilter());
			config = config.accept(new PriorityFilter());
			config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
			config = config.accept(new TypeInferenceSupremumFilter());
			config = config.accept(new PreferAvoidFilter());
			config = config.accept(new FlattenListsFilter());
			config = config.accept(new AmbDuplicateFilter());
			// last resort disambiguation
			config = config.accept(new AmbFilter());
		} catch (TransformerException e) {
			String msg = "Cannot parse pattern: " + e.getLocalizedMessage();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, config.getFilename(), config.getLocation()));
		}
		return config;
	}
}
