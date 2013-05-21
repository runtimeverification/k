package org.kframework.parser;

import com.thoughtworks.xstream.XStream;
import org.kframework.compile.checks.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Term;
import org.kframework.kil.loader.*;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.*;
import org.kframework.parser.generator.*;
import org.kframework.parser.utils.ResourceExtractor;
import org.kframework.parser.utils.Sdf2Table;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

public class DefinitionLoader {
	public static org.kframework.kil.Definition loadDefinition(File mainFile, String lang, boolean autoinclude, DefinitionHelper definitionHelper) throws IOException, Exception {
		org.kframework.kil.Definition javaDef;
		File canoFile = mainFile.getCanonicalFile();

		String extension = FileUtil.getExtension(mainFile.getAbsolutePath());
		if (extension != null && (extension.equals(".xml") || extension.equals(".bin"))) {
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

			javaDef.preprocess(definitionHelper);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

		} else {
			javaDef = parseDefinition(mainFile, lang, autoinclude, definitionHelper);

			BinaryLoader.toBinary(javaDef, new FileOutputStream(definitionHelper.dotk.getAbsolutePath() + "/defx.bin"));

			if (GlobalSettings.xml) {
				XStream xstream = new XStream();
				xstream.aliasPackage("k", "org.kframework.kil");
				xstream.toXML(javaDef, new FileOutputStream(definitionHelper.dotk.getAbsolutePath() + "/defx.xml"));
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
	public static Definition parseDefinition(File mainFile, String mainModule, boolean autoinclude, DefinitionHelper definitionHelper) {
		try {
			// for now just use this file as main argument
			// ------------------------------------- basic parsing

			BasicParser bparser = new BasicParser(autoinclude);
			bparser.slurp(mainFile.getPath(), definitionHelper);

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

			new CheckVisitorStep<Definition>(new CheckListOfKDeprecation(definitionHelper), definitionHelper).check(def);

			def.preprocess(definitionHelper);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

			new CheckVisitorStep<Definition>(new CheckSyntaxDecl(definitionHelper), definitionHelper).check(def);
			new CheckVisitorStep<Definition>(new CheckListDecl(definitionHelper), definitionHelper).check(def);
			new CheckVisitorStep<Definition>(new CheckSortTopUniqueness(definitionHelper), definitionHelper).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Checks");

			// ------------------------------------- generate files
			ResourceExtractor.ExtractDefSDF(new File(definitionHelper.dotk + "/def"));
			ResourceExtractor.ExtractGroundSDF(new File(definitionHelper.dotk + "/ground"));

			ResourceExtractor.ExtractProgramSDF(new File(definitionHelper.dotk + "/pgm"));

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			if (!GlobalSettings.documentation) {
				String oldSdfPgm = "";
				if (new File(definitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf").exists())
					oldSdfPgm = FileUtil.getFileContent(definitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				String newSdfPgm = ProgramSDF.getSdfForPrograms(def, definitionHelper);

				FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf", newSdfPgm);
				newSdfPgm = FileUtil.getFileContent(definitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("File Gen Pgm");

				if (!oldSdfPgm.equals(newSdfPgm) || !new File(definitionHelper.dotk.getAbsoluteFile() + "/pgm/Program.tbl").exists()) {
					Sdf2Table.run_sdf2table(new File(definitionHelper.dotk.getAbsoluteFile() + "/pgm"), "Program");
					if (GlobalSettings.verbose)
						Stopwatch.sw.printIntermediate("Generate TBLPgm");
				}
			}

			def.accept(new AddAutoIncludedModulesVisitor(definitionHelper));
			def.accept(new CheckModulesAndFilesImportsDecl(definitionHelper));
			def.accept(new CollectModuleImportsVisitor(definitionHelper));

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			String oldSdf = "";
			if (new File(definitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(definitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");
			FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf", DefinitionSDF.getSdfForDefinition(def, definitionHelper));
			FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath() + "/ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def, definitionHelper));
			String newSdf = FileUtil.getFileContent(definitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("File Gen Def");

			if (!oldSdf.equals(newSdf) || !new File(definitionHelper.dotk.getAbsoluteFile() + "/def/Concrete.tbl").exists()
					|| !new File(definitionHelper.dotk.getAbsoluteFile() + "/ground/Concrete.tbl").exists()) {
				// Sdf2Table.run_sdf2table(new File(definitionHelper.dotk.getAbsoluteFile() + "/def"), "Concrete");
				Thread t1 = Sdf2Table.run_sdf2table_parallel(new File(definitionHelper.dotk.getAbsoluteFile() + "/def"), "Concrete");
				if (!GlobalSettings.documentation) {
					Thread t2 = Sdf2Table.run_sdf2table_parallel(new File(definitionHelper.dotk.getAbsoluteFile() + "/ground"), "Concrete");
					t2.join();
				}
				t1.join();
				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("Generate TBLDef");
			}
			// ------------------------------------- import files in Stratego
			org.kframework.parser.concrete.KParser.ImportTbl(definitionHelper.dotk.getAbsolutePath() + "/def/Concrete.tbl");

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Importing Files");

			// ------------------------------------- parse configs
			JavaClassesFactory.startConstruction(definitionHelper);
			def = (Definition) def.accept(new ParseConfigsFilter(definitionHelper));
			JavaClassesFactory.endConstruction();
			def.accept(new CollectConfigCellsVisitor(definitionHelper));

			// sort List in streaming cells
			new CheckVisitorStep<Definition>(new CheckStreams(definitionHelper), definitionHelper).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Parsing Configs");

			// ----------------------------------- parse rules
			JavaClassesFactory.startConstruction(definitionHelper);		
			def = (Definition) def.accept(new ParseRulesFilter(definitionHelper));
			JavaClassesFactory.endConstruction();

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

	public static Term parseCmdString(String content, String sort, String filename, DefinitionHelper definitionHelper) throws TransformerException {
		if (!definitionHelper.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}
		String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);
		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(definitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);

		JavaClassesFactory.startConstruction(definitionHelper);
		org.kframework.kil.ASTNode config = (Term) JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		// TODO: reject rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(definitionHelper), definitionHelper).check(config);
		config = config.accept(new SentenceVariablesFilter(definitionHelper));
		config = config.accept(new CellEndLabelFilter(definitionHelper));
		// config = config.accept(new InclusionFilter(localModule));
		config = config.accept(new CellTypesFilter(definitionHelper));
		// config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(definitionHelper));
		config = config.accept(new CorrectCastPriorityFilter(definitionHelper));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		config = config.accept(new TypeSystemFilter(definitionHelper));
		config = config.accept(new PriorityFilter(definitionHelper));
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(definitionHelper), definitionHelper));
		config = config.accept(new TypeInferenceSupremumFilter(definitionHelper));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(definitionHelper), definitionHelper));
		config = config.accept(new PreferAvoidFilter(definitionHelper));
		config = config.accept(new FlattenListsFilter(definitionHelper));
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		// last resort disambiguation
		config = config.accept(new AmbFilter(definitionHelper));

		return (Term) config;
	}

	public static ASTNode parsePattern(String pattern, String filename, DefinitionHelper definitionHelper) throws TransformerException {
		if (!definitionHelper.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString("rule " + pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(definitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		XmlLoader.writeXmlFile(doc, definitionHelper.kompiled + "/pattern.xml");

		JavaClassesFactory.startConstruction(definitionHelper);
		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		// TODO: reject rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(definitionHelper), definitionHelper).check(config);
		config = config.accept(new SentenceVariablesFilter(definitionHelper));
		config = config.accept(new CellEndLabelFilter(definitionHelper));
		// config = config.accept(new InclusionFilter(localModule));
		config = config.accept(new CellTypesFilter(definitionHelper));
		// config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(definitionHelper));
		config = config.accept(new CorrectCastPriorityFilter(definitionHelper));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		config = config.accept(new TypeSystemFilter(definitionHelper));
		config = config.accept(new PriorityFilter(definitionHelper));
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(definitionHelper), definitionHelper));
		config = config.accept(new TypeInferenceSupremumFilter(definitionHelper));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(definitionHelper), definitionHelper));
		config = config.accept(new PreferAvoidFilter(definitionHelper));
		config = config.accept(new FlattenListsFilter(definitionHelper));
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		// last resort disambiguation
		config = config.accept(new AmbFilter(definitionHelper));

		return config;
	}

	public static ASTNode parsePatternAmbiguous(String pattern, DefinitionHelper definitionHelper) throws TransformerException {
		if (!definitionHelper.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString("rule " + pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		//XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(definitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		XmlLoader.writeXmlFile(doc, definitionHelper.kompiled + "/pattern.xml");

		JavaClassesFactory.startConstruction(definitionHelper);		
		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();
		
		// TODO: don't allow rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(definitionHelper), definitionHelper).check(config);
		config = config.accept(new SentenceVariablesFilter(definitionHelper));
		config = config.accept(new CellEndLabelFilter(definitionHelper));
		config = config.accept(new CellTypesFilter(definitionHelper));
		//config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(definitionHelper));
		config = config.accept(new CorrectCastPriorityFilter(definitionHelper));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new InclusionFilter(localModule));
		//config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		config = config.accept(new TypeSystemFilter(definitionHelper));
		//config = config.accept(new PriorityFilter());
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(definitionHelper), definitionHelper));
		config = config.accept(new TypeInferenceSupremumFilter(definitionHelper));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(definitionHelper), definitionHelper));
		//config = config.accept(new PreferAvoidFilter());
		config = config.accept(new FlattenListsFilter(definitionHelper));
		config = config.accept(new AmbDuplicateFilter(definitionHelper));
		// last resort disambiguation
		//config = config.accept(new AmbFilter());
		return config;
	}
}
