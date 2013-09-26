package org.kframework.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.List;

import org.kframework.compile.checks.CheckListDecl;
import org.kframework.compile.checks.CheckListOfKDeprecation;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxDecl;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.loader.AddAutoIncludedModulesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectModuleImportsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.basic.Basic;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
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


public class DefinitionLoader {
	public static Definition loadDefinition(File mainFile, String lang, boolean autoinclude, Context context) throws Exception {
		Definition javaDef;
		File canoFile = mainFile.getCanonicalFile();

		String extension = FileUtil.getExtension(mainFile.getAbsolutePath());
		if (".bin".equals(extension)) {
            javaDef = (Definition) BinaryLoader.fromBinary(new FileInputStream(canoFile));

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Load definition from binary");

			javaDef.preprocess(context);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

		} else {
			javaDef = parseDefinition(mainFile, lang, autoinclude, context);

			BinaryLoader.toBinary(javaDef, new FileOutputStream(context.dotk.getAbsolutePath() + "/defx-" + (GlobalSettings.javaBackend ? "java" : "maude") + ".bin"));
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
	public static Definition parseDefinition(File mainFile, String mainModule, boolean autoinclude, Context context) {
		try {
			// for now just use this file as main argument
			// ------------------------------------- basic parsing

			BasicParser bparser = new BasicParser(autoinclude);
			bparser.slurp(mainFile.getPath(), context);

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

			new CheckVisitorStep<Definition>(new CheckListOfKDeprecation(context), context).check(def);
			// HERE: add labels to sorts

			def.preprocess(context);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Preprocess");

			new CheckVisitorStep<Definition>(new CheckSyntaxDecl(context), context).check(def);
			new CheckVisitorStep<Definition>(new CheckListDecl(context), context).check(def);
			new CheckVisitorStep<Definition>(new CheckSortTopUniqueness(context), context).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Checks");

			// ------------------------------------- generate files
			ResourceExtractor.ExtractDefSDF(new File(context.dotk + "/def"));
			ResourceExtractor.ExtractGroundSDF(new File(context.dotk + "/ground"));

			ResourceExtractor.ExtractProgramSDF(new File(context.dotk + "/pgm"));

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			if (!GlobalSettings.documentation) {
				String oldSdfPgm = "";
				if (new File(context.dotk.getAbsolutePath() + "/pgm/Program.sdf").exists())
					oldSdfPgm = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				String newSdfPgm = ProgramSDF.getSdfForPrograms(def, context);

				FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/pgm/Program.sdf", newSdfPgm);
				newSdfPgm = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/pgm/Program.sdf");

				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("File Gen Pgm");

				if (!oldSdfPgm.equals(newSdfPgm) || !new File(context.dotk.getAbsoluteFile() + "/pgm/Program.tbl").exists()) {
					Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/pgm"), "Program");
					if (GlobalSettings.verbose)
						Stopwatch.sw.printIntermediate("Generate TBLPgm");
				}
			}

			def.accept(new AddAutoIncludedModulesVisitor(context));
			// def.accept(new CheckModulesAndFilesImportsDecl(context));
			def.accept(new CollectModuleImportsVisitor(context));

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			String oldSdf = "";
			if (new File(context.dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/def/Integration.sdf");
			FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/def/Integration.sdf", DefinitionSDF.getSdfForDefinition(def, context));
			FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def, context));
			String newSdf = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("File Gen Def");

			if (!oldSdf.equals(newSdf) || !new File(context.dotk.getAbsoluteFile() + "/def/Concrete.tbl").exists()
					|| !new File(context.dotk.getAbsoluteFile() + "/ground/Concrete.tbl").exists()) {
				// Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
				Thread t1 = Sdf2Table.run_sdf2table_parallel(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
				if (!GlobalSettings.documentation) {
					Thread t2 = Sdf2Table.run_sdf2table_parallel(new File(context.dotk.getAbsoluteFile() + "/ground"), "Concrete");
					t2.join();
				}
				t1.join();
				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("Generate TBLDef");
			}
			if (!GlobalSettings.fastKast) { // ------------------------------------- import files in Stratego
				org.kframework.parser.concrete.KParser.ImportTbl(context.dotk.getAbsolutePath() + "/def/Concrete.tbl");

				if (GlobalSettings.verbose)
					Stopwatch.sw.printIntermediate("Importing Files");
			}
			// ------------------------------------- parse configs
			JavaClassesFactory.startConstruction(context);
			def = (Definition) def.accept(new ParseConfigsFilter(context));
			JavaClassesFactory.endConstruction();
			def.accept(new CollectConfigCellsVisitor(context));

			// sort List in streaming cells
			new CheckVisitorStep<Definition>(new CheckStreams(context), context).check(def);

			if (GlobalSettings.verbose)
				Stopwatch.sw.printIntermediate("Parsing Configs");

			// ----------------------------------- parse rules
			JavaClassesFactory.startConstruction(context);
			def = (Definition) def.accept(new ParseRulesFilter(context));
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

	/**
	 * Parses a string representing a file with modules in it. Returns the complete parse tree. Any bubble rule has been parsed and disambiguated.
	 * 
	 * @param content
	 *            - the input string.
	 * @param filename
	 *            - only for error reporting purposes. Can be empty string.
	 * @param context
	 *            - the context for disambiguation purposes.
	 * @return A lightweight Definition element which contain all the definition items found in the string.
	 */
	public static Definition parseString(String content, String filename, Context context) {
		try {
			List<DefinitionItem> di = Basic.parse(filename, content, context);

			org.kframework.kil.Definition def = new org.kframework.kil.Definition();
			def.setItems(di);

			new CheckVisitorStep<Definition>(new CheckListOfKDeprecation(context), context).check(def);

			// ------------------------------------- import files in Stratego
			org.kframework.parser.concrete.KParser.ImportTbl(context.kompiled.getAbsolutePath() + "/def/Concrete.tbl");

			// ------------------------------------- parse configs
			JavaClassesFactory.startConstruction(context);
			def = (Definition) def.accept(new ParseConfigsFilter(context, false));
			JavaClassesFactory.endConstruction();

			// ----------------------------------- parse rules
			JavaClassesFactory.startConstruction(context);
			def = (Definition) def.accept(new ParseRulesFilter(context, false));
			JavaClassesFactory.endConstruction();

			return def;
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static Term parseCmdString(String content, String sort, String filename, Context context) throws TransformerException {
		if (!context.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}
		String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);
		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(context.kompiled.getAbsolutePath() + "/pgm.xml", parsed);

		JavaClassesFactory.startConstruction(context);
		org.kframework.kil.ASTNode config = (Term) JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		// TODO: reject rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(context), context).check(config);
		config = config.accept(new SentenceVariablesFilter(context));
		config = config.accept(new CellEndLabelFilter(context));
		// config = config.accept(new InclusionFilter(localModule));
		config = config.accept(new CellTypesFilter(context));
		// config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(context));
		config = config.accept(new CorrectCastPriorityFilter(context));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(context));
		config = config.accept(new TypeSystemFilter(context));
		config = config.accept(new PriorityFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context));
		config = config.accept(new TypeInferenceSupremumFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context));
		config = config.accept(new PreferAvoidFilter(context));
		config = config.accept(new FlattenListsFilter(context));
		config = config.accept(new AmbDuplicateFilter(context));
		// last resort disambiguation
		config = config.accept(new AmbFilter(context));

		return (Term) config;
	}

	public static ASTNode parsePattern(String pattern, String filename, Context context) throws TransformerException {
		if (!context.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(context.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		XmlLoader.writeXmlFile(doc, context.kompiled + "/pattern.xml");

		JavaClassesFactory.startConstruction(context);
		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		// TODO: reject rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(context), context).check(config);
		config = config.accept(new SentenceVariablesFilter(context));
		config = config.accept(new CellEndLabelFilter(context));
		// config = config.accept(new InclusionFilter(localModule));
		config = config.accept(new CellTypesFilter(context));
		// config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(context));
		config = config.accept(new CorrectCastPriorityFilter(context));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(context));
		config = config.accept(new TypeSystemFilter(context));
		config = config.accept(new PriorityFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context));
		config = config.accept(new TypeInferenceSupremumFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context));
		config = config.accept(new PreferAvoidFilter(context));
		config = config.accept(new FlattenListsFilter(context));
		config = config.accept(new AmbDuplicateFilter(context));
		// last resort disambiguation
		config = config.accept(new AmbFilter(context));

		return config;
	}

	/**
	 * Parses a string of the form: A => B when X [attributes], where the 'when' clause and the attributes can be absent.
	 * @param sentence The input string.
	 * @param filename Required for error reporting. Can be anything.
	 * @param context The context is required for disambiguation purposes.
	 * @return A {@link Sentence} element.
	 * @throws TransformerException
	 */
	public static ASTNode parseSentence(String sentence, String filename, Context context) throws TransformerException {
		if (!context.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(sentence);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		//		FileUtil.saveInFile(context.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		//		XmlLoader.writeXmlFile(doc, context.kompiled + "/pattern.xml");

		JavaClassesFactory.startConstruction(context);
		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(context), context).check(config);
		config = config.accept(new SentenceVariablesFilter(context));
		config = config.accept(new CellEndLabelFilter(context));
		// config = config.accept(new InclusionFilter(localModule, context));
		config = config.accept(new CellTypesFilter(context));
		config = config.accept(new CorrectRewritePriorityFilter(context));
		config = config.accept(new CorrectKSeqFilter(context));
		config = config.accept(new CorrectCastPriorityFilter(context));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		config = config.accept(new VariableTypeInferenceFilter(context));
		config = config.accept(new AmbDuplicateFilter(context));
		config = config.accept(new TypeSystemFilter(context));
		config = config.accept(new PriorityFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context));
		config = config.accept(new TypeInferenceSupremumFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context));
		config = config.accept(new PreferAvoidFilter(context));
		config = config.accept(new FlattenListsFilter(context));
		config = config.accept(new AmbDuplicateFilter(context));
		// last resort disambiguation
		config = config.accept(new AmbFilter(context));

		return config;
	}

	public static ASTNode parsePatternAmbiguous(String pattern, Context context) throws TransformerException {
		if (!context.initialized) {
			System.err.println("You need to load the definition before you call parsePattern!");
			System.exit(1);
		}

		String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
		Document doc = XmlLoader.getXMLDoc(parsed);

		// XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(context.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		XmlLoader.writeXmlFile(doc, context.kompiled + "/pattern.xml");

		JavaClassesFactory.startConstruction(context);
		ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		JavaClassesFactory.endConstruction();

		// TODO: don't allow rewrites
		new CheckVisitorStep<ASTNode>(new CheckListOfKDeprecation(context), context).check(config);
		config = config.accept(new SentenceVariablesFilter(context));
		config = config.accept(new CellEndLabelFilter(context));
		config = config.accept(new CellTypesFilter(context));
		// config = config.accept(new CorrectRewritePriorityFilter());
		config = config.accept(new CorrectKSeqFilter(context));
		config = config.accept(new CorrectCastPriorityFilter(context));
		// config = config.accept(new CheckBinaryPrecedenceFilter());
		// config = config.accept(new InclusionFilter(localModule));
		// config = config.accept(new VariableTypeInferenceFilter());
		config = config.accept(new AmbDuplicateFilter(context));
		config = config.accept(new TypeSystemFilter(context));
		// config = config.accept(new PriorityFilter());
		config = config.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context));
		config = config.accept(new TypeInferenceSupremumFilter(context));
		config = config.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context));
		// config = config.accept(new PreferAvoidFilter());
		config = config.accept(new FlattenListsFilter(context));
		config = config.accept(new AmbDuplicateFilter(context));
		// last resort disambiguation
		// config = config.accept(new AmbFilter());
		return config;
	}
}
