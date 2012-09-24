package org.kframework.utils;

import java.io.File;
import java.io.IOException;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.kil.Term;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewriteSortFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitFileCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.generator.basic.Definition;
import org.kframework.parser.generator.preprocessor.Preprocessor;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.utils.file.FileUtil;
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
			File dotk = new File(canoFile.getParent() + "/.k");
			dotk.mkdirs();
			javaDef = parseDefinition(lang, canoFile, dotk);
		}
		return javaDef;
	}

	public static org.kframework.kil.Definition parseDefinition(String mainModule, File canonicalFile, File dotk) throws IOException, Exception {
		Stopwatch sw = new Stopwatch();
		// ------------------------------------- basic parsing
		Definition def = new Definition();
		def.slurp(canonicalFile, true);
		def.setMainFile(canonicalFile);
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
		FileUtil.saveInFile(dotk.getAbsolutePath() + "/def/Integration.sdf", def.getSDFForDefinition());
		newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");

		if (GlobalSettings.verbose)
			sw.printIntermediate("File Gen Def    = ");

		if (!oldSdf.equals(newSdf))
			Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/def"), "K3Disamb");

		if (GlobalSettings.verbose)
			sw.printIntermediate("Generate TBLDef = ");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportSbs(dotk.getAbsolutePath() + "/Integration.sbs");
		org.kframework.parser.concrete.KParser.ImportCons(dotk.getAbsolutePath() + "/Integration.cons");
		org.kframework.parser.concrete.KParser.ImportTbl(dotk.getAbsolutePath() + "/def/K3Disamb.tbl");

		if (GlobalSettings.verbose)
			sw.printIntermediate("Importing Files = ");

		// ------------------------------------- parse configs
		FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cells", def.getCellsFromConfigAsStrategoTerm());
		org.kframework.parser.concrete.KParser.ImportCells(dotk.getAbsolutePath() + "/Integration.cells");

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

		org.kframework.kil.Definition javaDef = new org.kframework.kil.Definition((Element) preprocessedDef.getFirstChild());

		javaDef.accept(new UpdateReferencesVisitor());
		javaDef.accept(new CollectConsesVisitor());
		javaDef.accept(new CollectSubsortsVisitor());
		// disambiguation steps

		javaDef = (org.kframework.kil.Definition) javaDef.accept(new CellTypesFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new CorrectRewritePriorityFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new CorrectKSeqFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitFileCheckVisitor()));
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new VariableTypeInferenceFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new AmbDuplicateFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new TypeSystemFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new TypeInferenceSupremumFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new FlattenListsFilter());
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new CorrectRewriteSortFilter());
		// last resort disambiguation
		javaDef = (org.kframework.kil.Definition) javaDef.accept(new AmbFilter());

		if (GlobalSettings.verbose)
			sw.printIntermediate("Disambiguate    = ");

		javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddEmptyLists());

		return javaDef;
	}

	public static Term parseCmdString(String content, String sort) throws Exception {
		String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
		System.out.println("Parsed: " + parsed);
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
