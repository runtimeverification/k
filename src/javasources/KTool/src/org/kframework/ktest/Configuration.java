package org.kframework.ktest;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

public class Configuration {

	// file separator
	public static final String FILE_SEPARATOR = System.getProperty("file.separator");
	public static final String USER_DIR = System.getProperty("user.dir");
    public static boolean REPORT = false;

    // timeout in miliseconds - this is mostly used by Jenkins
	public static long KOMPILE_ALL_TIMEOUT = 60 * 60; //60 minutes

	// jenkins junit reports directory
	public static String JR = "junit-reports";

	// the configuration file which is active when !SINGLE_DEF_MODE
	public static String CONFIG = null;

	// these options are used to create a task for testing
	// a single K definition and its programs directly from command line
	public static boolean SINGLE_DEF_MODE = false;
	// mandatory
	public static String KDEF = USER_DIR;
	// programs
	public static String PGM_DIR = null; //USER_DIR;
	public static List<String> EXTENSIONS = new LinkedList<String>();
	// optional
	public static boolean PDF = true;
	public static String RESULTS_FOLDER = null; //USER_DIR;
	public static List<String> EXCLUDE_PROGRAMS = null;

	// XML tag and attribute names used for parsing config.xml
	// Some of these constants are used as ktest option names (see below)
	public static final String PARSER_HOME = "parser-home";
	public static final String MESSAGE = "message";
	public static final String ERROR = "error";
	public static final String SYSTEM_ERR = "system-err";
	public static final String SYSTEM_OUT = "system-out";
	public static final String TIME = "time";
	public static final String STATUS = "status";
	public static final String TESTCASE = "testcase";
	public static final String TESTSUITE = "testsuite";
	public static final String KRUN_OPTION = "krun-option";
	public static final String ALL_PROGRAMS = "all-programs";
	public static final String KOMPILE_OPTION = "kompile-option";
	public static final String PROGRAM = "program";
	public static final String NAME = "name";
	public static final String EXCLUDE = "exclude";
	public static final String EXTENSIONS2 = "extension";
	public static final String RECURSIVE = "recursive";
	public static final String YES = "yes";
	public static final String TITLE = "title";
	public static final String REPORT_DIR = "report-dir";
	public static final String RESULTS = "results";
	public static final String PROGRAMS_DIR = "programs";
	public static final String LANGUAGE = "definition";
	public static final String IN = ".in";
	public static final String ERR = ".err";
	public static final String OUT = ".out";
	public static final String VALUE = "value";
	public static final String UNIX_ONLY = "unixOnly";
	public static final String TEST = "test";
    public static final String TESTS = "tests";
    public static boolean KOMPILE = true;
    public static boolean PROGRAMS = true;
	public static boolean VERBOSE = false;

	// ktest command line option names
	public static final String HELP_OPTION = "help";
	public static final String HELP_EXPERIMENTAL_OPTION = "help-experimental";
	public static final String VERSION_OPTION = "version";
	public static final String DIRECTORY_OPTION = "directory";
	public static final String PROGRAMS_OPTION = PROGRAMS_DIR;
	public static final String EXCLUDE_OPTION = EXCLUDE;
	public static final String EXTENSIONS_OPTION = EXTENSIONS2;
    public static final String REPORT_OPTION = "report";
	public static final String RESULTS_OPTION = RESULTS;
    public static final String SKIP_OPTION = "skip";
	public static final String VERBOSE_OPTION = "verbose";
    public static final String TIMEOUT_OPTION = "timeout";

	// program name
	public static final String KOMPILE_STEP = "kompile";
	public static final String PDF_STEP = "pdf";
	public static final String PROGRAMS_STEP = "programs";
	public static final String PROCESSES_OPTION = "threads";

	// some error messages
	public static String PGM_ERROR = "Please check the programs folder from configuration file.";
	public static String DEF_ERROR = "Please check the definition folder from configuration file.";
	public static String RES_ERROR = "Please check the results folder from configuration file.";

	// get the K instalation home directory
	private static String getKHome() {
		return new File(KTest.class.getProtectionDomain().getCodeSource()
				.getLocation().getPath()).getParentFile().getParentFile()
				.getParentFile().getPath();
	}

	public static String getKompile() {
		return getExecutable("kompile");
	}

	public static String getKrun() {
		return getExecutable("krun");
	}

	// builds the path for a dist/bin executable depeding on the os
	private static String getExecutable(String exe) {
		String os = System.getProperty("os.name").toLowerCase();
		if (os.contains("win")) {
			return getKHome() + FILE_SEPARATOR + "bin" + FILE_SEPARATOR + exe + ".bat";
		}
		return getKHome() + FILE_SEPARATOR + "bin" + FILE_SEPARATOR + exe;
	}
}
