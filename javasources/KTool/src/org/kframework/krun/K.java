package org.kframework.krun;

import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.krun.api.SearchType;

import java.io.File;
import java.io.IOException;
import java.util.Properties;

public class K {

	public static boolean verbose = false;

	// os specific
	public static final String userdir = System.getProperty("user.dir");
	public static final String fileSeparator = System.getProperty("file.separator");
	public static final String lineSeparator = System.getProperty("line.separator");
	public static final String k_base = KPaths.getKBase(false);

	public static String kdir;
	static {
		if (DefinitionHelper.dotk == null) {
			DefinitionHelper.dotk = new File(userdir + File.separator + ".k");		
		}
		try {
			kdir = DefinitionHelper.dotk.getCanonicalPath();
			setKDir();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public static String krunDir, krunTempDir, maude_in, maude_out, maude_err, kast_in, maude_output, processed_maude_output, krun_output;

	public static void setKDir() {
		krunDir = kdir + fileSeparator + "krun";
		krunTempDir = kdir + fileSeparator + FileUtil.generateUniqueFolderName("krun");
		maude_in = krunTempDir + fileSeparator + "maude_in.maude";
		maude_out = krunTempDir + fileSeparator + "maude_out.txt";
		maude_err = krunTempDir + fileSeparator + "maude_err.txt";

		// kast
		kast_in = krunTempDir + fileSeparator + "kast_in.txt";

		//where to write the XML output from Maude
		maude_output = krunTempDir + fileSeparator + "maudeoutput.xml";
		processed_maude_output = krunTempDir + fileSeparator + "maudeoutput_simplified.xml";
	
		// where to write the pretty-printed output of jkrun
		krun_output = krunTempDir + fileSeparator + "krun_output";
	}

	// the default values for jkrun commandline options
	public static String desk_file;
	public static String pgm;
	public static String term = null;
	public static String k_definition = null;
	public static String main_module;
	public static String syntax_module;
	public static String parser = "kast";
	public static String compiled_def;
	public static String maude_cmd = "erewrite";
	public static String output_mode = "pretty";
	//public static String xsearch_pattern = "=>! B:Bag";
	public static String pattern = "<generatedTop> B:Bag </generatedTop> [anywhere]";
	public static SearchType searchType = SearchType.FINAL;
	public static String bound;
	public static String depth;
	public static String rule_labels = "";
	public static String model_checking = "";
	public static String output = "";

	// variables to store if that specific option was set; also set default values for options
	public static boolean help = false;
	public static boolean version = false;
	public static boolean io = true;
	public static boolean statistics = false;
	public static boolean color = true;
	public static boolean do_search = false;
	public static boolean showSearchGraph = false;
	//apply parenthesis by default
	public static boolean parens = true;
	public static boolean log_io = false;
	public static boolean debug = false;
	public static boolean guidebug = false;
	public static boolean trace = false;
	public static boolean profile = false;
	//don't delete temp folders created by krun by default
	public static boolean deleteTempDir = false;


	public static Properties configuration_variables = new Properties();
	public static Properties cfg_parsers = new Properties();	

	public static Definition definition;
	public static Configuration kompiled_cfg;

	public static int counter = 0;
	public static int stateCounter = 0;

	public static String backend = "maude";
}
