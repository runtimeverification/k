package org.kframework.krun;

import java.util.Properties;

public class K {

	public static boolean verbose = false;

	// os specific
	public static final String userdir = System.getProperty("user.dir");
	public static final String fileSeparator = System.getProperty("file.separator");
	public static final String lineSeparator = System.getProperty("line.separator");
	public static final String k_base = KPaths.getKBase(false);

	public static String kdir = userdir + fileSeparator + ".k";
	public static final String krunDir = kdir + fileSeparator + "krun";
	public static final String krunTempDir = kdir + fileSeparator + FileUtil.generateUniqueFolderName("krun");
	public static final String maude_in = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("maude_in.maude");
	public static final String maude_out = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("maude_out.txt");
	public static final String maude_err = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("maude_err.txt");

	// kast
	public static final String kast_in = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("kast_in.txt");

	//where to write the XML output from Maude
	public static final String maude_output = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("maudeoutput.xml");
	public static final String processed_maude_output = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("maudeoutput_simplified.xml");
	
	// where to write the pretty-printed output of jkrun
	public static final String krun_output = krunTempDir + fileSeparator + FileUtil.generateUniqueFileName("krun_output.txt");

	// the default values for jkrun commandline options
	public static String desk_file;
	public static String pgm;
	public static String k_definition;
	public static String main_module;
	public static String syntax_module;
	public static String parser = "kast";
	public static String compiled_def;
	public static String maude_cmd = "erewrite";
	public static String output_mode = "pretty";
	//public static String xsearch_pattern = "=>! B:Bag";
	public static String pattern = "=>! B:Bag";
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
	//apply parenthesis by default
	public static boolean parens = true;
	public static boolean log_io = false;
	public static boolean debug = false;
	public static boolean trace = false;
	//delete temp folders created by krun by default
	public static boolean deleteTempDir = true;


	public static Properties configuration_variables = new Properties();
	
}
