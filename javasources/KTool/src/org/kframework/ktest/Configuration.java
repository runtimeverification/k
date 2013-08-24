package org.kframework.ktest;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.kframework.krun.FileUtil;

public class Configuration {

	// file separator
	public static final String FS = System.getProperty("file.separator");

	// timeout in miliseconds - this is mostly used by Jenkins
	public static long KOMPILE_ALL_TIMEOUT = 120;

	// jenkins junit reports directory
	public static String JR = "junit-reports";

	// the configuration file which is active when !SINGLE_DEF_MODE
	public static String CONFIG = null;

	// these options are used to create a task for testing
	// a single K definition and its programs directly from command line
	public static boolean SINGLE_DEF_MODE = false;
	// mandatory
	public static String KDEF = System.getProperty("user.dir");
	// programs
	public static String PGM_DIR = System.getProperty("user.dir");
	public static List<String> EXTENSIONS = new LinkedList<String>();
	// optional
	public static boolean PDF = true;
	public static String RESULTS_FOLDER = System.getProperty("user.dir");
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
	public static final String EXTENSIONS2 = "extensions";
	public static final String RECURSIVE = "recursive";
	public static final String YES = "yes";
	public static final String PDF2 = "pdf";
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

	// ktest command line option names
	public static final String HELP_OPTION = "help";
	public static final String VERSION_OPTION = "version";
	public static final String LANGUAGE_OPTION = LANGUAGE;
	public static final String CONFIG_OPTION = "config";
	public static final String PROGRAMS_OPTION = PROGRAMS_DIR;
	public static final String EXCLUDE_OPTION = EXCLUDE;
	public static final String EXTENSIONS_OPTION = EXTENSIONS2;
	public static final String RESULTS_OPTION = RESULTS;

	// program name
	public static final String KTEST = "ktest";

	// help details
	public static String DETAILED_HELP_MESSAGE = getReadme();

	// some error messages
	public static String PGM_ERROR = "Please check the programs folder from configuration file.";
	public static String DEF_ERROR = "Please check the definition folder from configuration file.";
	public static String RES_ERROR = "Please check the results folder from configuration file.";

	// get the K instalation home directory
	public static String getKHome() {
		return new File(KTest.class.getProtectionDomain().getCodeSource()
				.getLocation().getPath()).getParentFile().getParentFile()
				.getParentFile().getParentFile().getPath();
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
			return getKHome() + FS + "dist" + FS + "bin" + FS + exe + ".bat";
		}
		return getKHome() + FS + "dist" + FS + "bin" + FS + exe;
	}
	
	public static String getReadme() {
		return FileUtil.getFileContent(getKHome() + FS + "tests" + FS + "README");
	}
}
