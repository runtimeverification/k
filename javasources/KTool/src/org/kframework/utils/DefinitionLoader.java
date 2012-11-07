package org.kframework.utils;

import java.io.File;
import java.io.IOException;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.kil.Definition;
import org.kframework.kil.Term;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.generator.AddConsesVisitor;
import org.kframework.parser.generator.BasicParser;
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
	public static org.kframework.kil.Definition loadDefinition(File mainFile, String lang) throws IOException, Exception {
		org.kframework.kil.Definition javaDef;
		File canoFile = mainFile.getCanonicalFile();

		if (FileUtil.getExtension(mainFile.getAbsolutePath()).equals(".xml")) {
			// unmarshalling
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			javaDef = (org.kframework.kil.Definition) xstream.fromXML(canoFile);
			javaDef.preprocess();

		} else {
			javaDef = parseDefinition(mainFile, lang);
		}
		return javaDef;
	}

	/**
	 * TODO: make this the new basic parsing step. 1. slurp 2. gen files 3. gen TBLs 4. import files in stratego 5. parse configs 6. parse rules 7. ???
	 * 
	 * @param mainFile
	 * @param mainModule
	 * @return
	 */
	public static Definition parseDefinition(File mainFile, String mainModule) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			// ------------------------------------- basic parsing

			BasicParser bparser = new BasicParser();
			bparser.slurp(mainFile.getPath());

			// transfer information from the BasicParser object, to the Definition object
			org.kframework.kil.Definition def = new org.kframework.kil.Definition();
			def.setMainFile(mainFile.getCanonicalPath());
			def.setMainModule(mainModule);
			def.setModulesMap(bparser.getModulesMap());
			def.setItems(bparser.getModuleItems());

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

			def.accept(new UpdateReferencesVisitor());
			def.accept(new AddConsesVisitor());
			def.accept(new CollectConsesVisitor());
			def.accept(new CollectSubsortsVisitor());

			if (GlobalSettings.verbose)
				sw.printIntermediate("Basic Parsing");

			// ------------------------------------- generate files
			ResourceExtractor.ExtractAllSDF(DefinitionHelper.dotk);

			ResourceExtractor.ExtractProgramSDF(DefinitionHelper.dotk);

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			String oldSdf = "";
			if (new File(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf").exists())
				oldSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

			// make a set of all the syntax modules
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf", ProgramSDF.getSdfForPrograms(def));

			String newSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/pgm/Program.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Pgm");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/pgm"), "Program");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLPgm");

			// ------------------------------------- generate parser TBL
			// cache the TBL if the sdf file is the same
			oldSdf = "";
			if (new File(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
				oldSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");
			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf", DefinitionSDF.getSdfForPrograms(def));
			newSdf = FileUtil.getFileContent(DefinitionHelper.dotk.getAbsolutePath() + "/def/Integration.sdf");

			if (GlobalSettings.verbose)
				sw.printIntermediate("File Gen Def");

			if (!oldSdf.equals(newSdf))
				Sdf2Table.run_sdf2table(new File(DefinitionHelper.dotk.getAbsoluteFile() + "/def"), "Concrete");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Generate TBLDef");

			// ------------------------------------- import files in Stratego
			org.kframework.parser.concrete.KParser.ImportTbl(DefinitionHelper.dotk.getAbsolutePath() + "/def/Concrete.tbl");

			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files");

			// ------------------------------------- parse configs
			def = (Definition) def.accept(new ParseConfigsFilter());
			def.accept(new CollectConfigCellsVisitor());

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Configs");

			// ----------------------------------- parse rules
			def = (Definition) def.accept(new ParseRulesFilter());

			if (GlobalSettings.verbose)
				sw.printIntermediate("Parsing Rules");

			return def;
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	public static Term parseCmdString(String content, String sort) throws Exception {
		String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);
		XmlLoader.addFilename(doc.getFirstChild(), "Command Line Argument");
		XmlLoader.reportErrors(doc);

		org.kframework.kil.Term javaDef = (Term) JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());

		javaDef = (org.kframework.kil.Term) javaDef.accept(new CellTypesFilter());
		// javaDef = (org.kframework.kil.Term) javaDef.accept(new CorrectRewritePriorityFilter()); // not the case, as it should be a ground term
		javaDef = (org.kframework.kil.Term) javaDef.accept(new CorrectKSeqFilter());
		// javaDef = (org.kframework.kil.Term) javaDef.accept(new BestFitFilter(new GetFitnessUnitFileCheckVisitor()));
		// javaDef = (org.kframework.kil.Term) javaDef.accept(new VariableTypeInferenceFilter());
		javaDef = (org.kframework.kil.Term) javaDef.accept(new AmbDuplicateFilter());
		javaDef = (org.kframework.kil.Term) javaDef.accept(new TypeSystemFilter());
		javaDef = (org.kframework.kil.Term) javaDef.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
		javaDef = (org.kframework.kil.Term) javaDef.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
		javaDef = (org.kframework.kil.Term) javaDef.accept(new TypeInferenceSupremumFilter());
		javaDef = (org.kframework.kil.Term) javaDef.accept(new FlattenListsFilter());
		// javaDef = (org.kframework.kil.Term) javaDef.accept(new CorrectRewriteSortFilter());
		// last resort disambiguation
		javaDef = (org.kframework.kil.Term) javaDef.accept(new AmbFilter());
		javaDef = (org.kframework.kil.Term) javaDef.accept(new AddEmptyLists());

		return javaDef;
	}
}
