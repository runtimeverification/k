package ro.uaic.fmse.jkrun;


public class K {

	public static boolean verbose = false;

	// os specific
	public static String userdir = System.getProperty("user.dir");
	public static String fileSeparator = System.getProperty("file.separator");
	public static String lineSeparator = System.getProperty("line.separator");
	//public static String k_base = System.getenv("K_BASE");
	public static String k_base = KPaths.getKBase(false);

	public static String kdir = userdir + fileSeparator + ".k";
	public static String maude_in = kdir + fileSeparator + "maude_in.txt";
	public static String maude_out = kdir + fileSeparator + "maude_out.txt";
	public static String maude_err = kdir + fileSeparator + "maude_err.txt";

	// maude
	public static String maude = "maude";

	// kast
	public static String kast = k_base + K.fileSeparator + "bin" + K.fileSeparator + "kast";

	public static String maude_io_cmd = "io-cmd.maude";
	public static String maude_output = "maudeoutput.xml";
	// where to write the pretty-printed output of jkrun
	public static String krun_output = "krun_output.txt";

	// the default values for options from here correspond to the ones from the desk file
	// arguments to jkrun commandline options
	public static String desk_file;
	public static String pgm;
	public static String k_definition;
	public static String main_module;
	public static String syntax_module;
	public static String parser = "kast";
	public static String compiled_def;
	public static String maude_cmd = "erewrite";
	public static String output_mode = "pretty";
	public static String xsearch_pattern = "=>! B:Bag";
	public static String rule_labels = "";

	// variables to store if that specific option was set; also set default values for options
	public static boolean help = false;
	public static boolean version = false;
	public static boolean io = true;
	public static boolean statistics = false;
	public static boolean color = true;
	public static boolean do_search = false;
	public static boolean parens = false;
	public static boolean log_io = false;
	public static boolean debug = false;
	public static boolean trace = false;

}
