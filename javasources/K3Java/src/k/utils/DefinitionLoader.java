package k.utils;

import java.io.File;
import java.io.IOException;

import k3.basic.Definition;

import org.kframework.disambiguate.AmbDuplicateFilter;
import org.kframework.disambiguate.AmbFilter;
import org.kframework.disambiguate.BestFitFilter;
import org.kframework.disambiguate.CellTypesFilter;
import org.kframework.disambiguate.CorrectKSeqFilter;
import org.kframework.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.disambiguate.CorrectRewriteSortFilter;
import org.kframework.disambiguate.FlattenListsFilter;
import org.kframework.disambiguate.GetFitnessUnitFileCheckVisitor;
import org.kframework.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.disambiguate.TypeSystemFilter;
import org.kframework.disambiguate.VariableTypeInferenceFilter;
import org.kframework.lists.EmptyListsVisitor;
import org.kframework.loader.CollectConsesVisitor;
import org.kframework.loader.CollectSubsortsVisitor;
import org.kframework.loader.UpdateReferencesVisitor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.pp.Preprocessor;
import ro.uaic.info.fmse.utils.file.FileUtil;

import com.thoughtworks.xstream.XStream;

public class DefinitionLoader {
	public static org.kframework.k.Definition loadDefinition(File mainFile, String lang) throws IOException, Exception {
		org.kframework.k.Definition javaDef;
		File canoFile = mainFile.getCanonicalFile();

		if (FileUtil.getExtension(mainFile.getAbsolutePath()).equals(".xml")) {
			// unmarshalling
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			javaDef = (org.kframework.k.Definition) xstream.fromXML(canoFile);
			javaDef.preprocess();

		} else {
			File dotk = new File(canoFile.getParent() + "/.k");
			dotk.mkdirs();
			javaDef = parseDefinition(lang, canoFile, dotk);
		}
		return javaDef;
	}

	public static org.kframework.k.Definition parseDefinition(String mainModule, File canonicalFile, File dotk) throws IOException, Exception {
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

		org.kframework.k.Definition javaDef = new org.kframework.k.Definition((Element) preprocessedDef.getFirstChild());

		javaDef.accept(new UpdateReferencesVisitor());
		javaDef.accept(new CollectConsesVisitor());
		javaDef.accept(new CollectSubsortsVisitor());
		// disambiguation steps

		if (GlobalSettings.tempDisamb) {
			javaDef = (org.kframework.k.Definition) javaDef.accept(new CellTypesFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new CorrectRewritePriorityFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new CorrectKSeqFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitFileCheckVisitor()));
			javaDef = (org.kframework.k.Definition) javaDef.accept(new VariableTypeInferenceFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new AmbDuplicateFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new TypeSystemFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitTypeCheckVisitor()));
			javaDef = (org.kframework.k.Definition) javaDef.accept(new BestFitFilter(new GetFitnessUnitKCheckVisitor()));
			javaDef = (org.kframework.k.Definition) javaDef.accept(new TypeInferenceSupremumFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new FlattenListsFilter());
			javaDef = (org.kframework.k.Definition) javaDef.accept(new CorrectRewriteSortFilter());
			if (GlobalSettings.verbose)
				sw.printIntermediate("Disambiguate    = ");
		}
		// last resort disambiguation
		javaDef = (org.kframework.k.Definition) javaDef.accept(new AmbFilter());

		javaDef = (org.kframework.k.Definition) javaDef.accept(new EmptyListsVisitor());

		return javaDef;
	}
}
