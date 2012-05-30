/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package klint;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.pp.Preprocessor;

/**
 *
 * @author fotanus
 */
public class Klint {

private static HashMap parameters = new HashMap();

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) throws IOException {
		if(processParameters(args)) {
			String fileName = (String) parameters.get("sourceFile");
			File sourceFile = new File(fileName).getCanonicalFile();

			k3.basic.Definition def = new k3.basic.Definition();
			def.slurp(sourceFile, true);
			def.setMainFile(sourceFile);
			def.addConsToProductions();
			def.parseRules();

			Preprocessor preprocessor = new Preprocessor();
			Document preprocessedDef = preprocessor.run(def.getDefAsXML());
			Definition javaDef = new Definition((Element) preprocessedDef.getFirstChild());
			System.out.println(javaDef.toString());

		} else {
			System.exit(1);
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
}
