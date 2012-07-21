package klint;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.logging.Level;
import java.util.logging.Logger;
import k.utils.FileUtil;
import k.utils.ResourceExtractor;
import k.utils.Sdf2Table;
import k.utils.XmlLoader;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.loader.AmbFilter;
import ro.uaic.info.fmse.loader.CollectConsesVisitor;
import ro.uaic.info.fmse.loader.CollectSubsortsVisitor;
import ro.uaic.info.fmse.loader.UpdateReferencesVisitor;
import ro.uaic.info.fmse.pp.Preprocessor;

/**
 *
 * @author fotanus
 * Main class for Klint tool. Responsable for the user interface and file parsing.
 */
public class Klint {

private static HashMap parameters = new HashMap();

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
		try {
			if(processParameters(args)) {

				String fileName = (String) parameters.get("sourceFile");
				File sourceFile = new File(fileName).getCanonicalFile();

				File dotk = new File(sourceFile.getParent() + "/.k");
				dotk.mkdirs();
				String lang = sourceFile.getName().replaceFirst("\\.[a-zA-Z]+$", "").toUpperCase();
							
				Definition javaDef = parseDefinition(lang, sourceFile, dotk);

				//TODO: Find a way to run a instance of each class that extends KlintRule class.
				KlintRule lintRule = new UnusedName(javaDef);
				lintRule.run();
				
				lintRule = new UnusedSyntax(javaDef);
				lintRule.run();
				
				//System.out.println(javaDef);
	
			
			} else {
				System.exit(1);
			}
		} catch (Exception ex) {
				Logger.getLogger(Klint.class.getName()).log(Level.SEVERE, null, ex);
		}		
    }
	
	/**
	 * parse the parameters and set the class variables to the correct values
	 * @param args
	 * @return returns true if there are no syntax errors on parameters
	 */
	private static boolean processParameters(String[] args) {
		if(args.length < 1){
			printUsage();
			return false;
		}

		File source = new File(args[0]);
		if(!source.exists() || !source.canRead()) {
			System.out.println("File not found: " + args[0]);
			printUsage();
			return false;
		}
		else{
			parameters.put("sourceFile", args[0]);

		}


		return true;
	}


	/**
	 * prints usage for klint tool
	 */
	private static void printUsage() {
		System.out.println("klin file.k [options]");
	}

	
	
		
	
	
	
	
	/**
	 * This method is a base copy from javasources/K3Java/src/k3/basic/Definition.java
	 * I strongly think this should be somewhere else since it parses a file to a AST.
	 * 
	 * TODO: Move somewhere
	 * 
	 * @param mainModule
	 * @param canonicalFiletest.k
	 * @param dotk
	 * @return The AST
	 * @throws IOException
	 * @throws Exception 
	 */
	private static Definition parseDefinition(String mainModule, File canonicalFile, File dotk) throws IOException, Exception {
	
		// ------------------------------------- basic parsing
		k3.basic.Definition def = new k3.basic.Definition();
		def.slurp(canonicalFile, true);
		def.setMainFile(canonicalFile);
		def.setMainModule(mainModule);
		def.addConsToProductions();

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

		if (!oldSdf.equals(newSdf))
			Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/pgm"), "Program");

		// generate a copy for the definition and modify it to generate the intermediate data
		k3.basic.Definition def2 = def.clone();// (Definition) Cloner.copy(def);
		def2.makeConsLists();

		FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.sbs", def2.getSubsortingAsStrategoTerms());
		FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cons", def2.getConsAsStrategoTerms());

		// ------------------------------------- generate parser TBL
		// cache the TBL if the sdf file is the same
		oldSdf = "";
		if (new File(dotk.getAbsolutePath() + "/def/Integration.sdf").exists())
			oldSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");
		FileUtil.saveInFile(dotk.getAbsolutePath() + "/def/Integration.sdf", def2.getSDFForDefinition());
		newSdf = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def/Integration.sdf");

		if (!oldSdf.equals(newSdf))
			Sdf2Table.run_sdf2table(new File(dotk.getAbsoluteFile() + "/def"), "K3Disamb");

		// ------------------------------------- import files in Stratego
		k3parser.KParser.ImportSbs(dotk.getAbsolutePath() + "/Integration.sbs");
		k3parser.KParser.ImportCons(dotk.getAbsolutePath() + "/Integration.cons");
		k3parser.KParser.ImportTbl(dotk.getAbsolutePath() + "/def/K3Disamb.tbl");

		
		// ------------------------------------- parse configs
		FileUtil.saveInFile(dotk.getAbsolutePath() + "/Integration.cells", def.getCellsFromConfigAsStrategoTerm());
		k3parser.KParser.ImportCells(dotk.getAbsolutePath() + "/Integration.cells");

		
		// ----------------------------------- parse rules
		def.parseRules();

		// ----------------------------------- preprocessiong steps
		Preprocessor preprocessor = new Preprocessor();
		Document preprocessedDef = preprocessor.run(def.getDefAsXML());

		XmlLoader.writeXmlFile(preprocessedDef, dotk.getAbsolutePath() + "/def.xml");
		ro.uaic.info.fmse.k.Definition javaDef = new ro.uaic.info.fmse.k.Definition((Element) preprocessedDef.getFirstChild());

		javaDef.accept(new UpdateReferencesVisitor());
		javaDef.accept(new CollectConsesVisitor());
		javaDef.accept(new CollectSubsortsVisitor());
		javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new AmbFilter());

	//	javaDef = (ro.uaic.info.fmse.k.Definition) javaDef.accept(new FlattenListsFilter());
		
		return javaDef;
		// ----------------------------------- preprocessiong steps
		
	

	}
}
