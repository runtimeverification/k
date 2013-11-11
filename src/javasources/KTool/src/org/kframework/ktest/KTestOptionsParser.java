package org.kframework.ktest;

import org.apache.commons.cli.*;
import org.kframework.utils.ActualPosixParser;

import java.util.ArrayList;

public class KTestOptionsParser {

	private final Options options;
	// For printing help messages: options = optionsStandard + optionsExperimental
	private final Options optionsStandard;
	private final Options optionsExperimental;
	private final ArrayList<Option> optionList = new ArrayList<Option>();

	// wrapper function to add an option
	private void addOptionWrapper(Option opt, boolean isStandard) {
		// for parsing command-line options
		options.addOption(opt);
		// for printing help messages
		optionList.add(opt);
		if (isStandard) {
			optionsStandard.addOption(opt);
		} else {
			optionsExperimental.addOption(opt);
		}
	}
	// add a standard option
	private void addOptionS(Option opt) {
		addOptionWrapper(opt, true);
	}
	// add an experimental option
	private void addOptionE(Option opt) {
		addOptionWrapper(opt, false);
	}

	public KTestOptionsParser() {
		options = new Options();
		optionsStandard = new Options();
		optionsExperimental = new Options();
		
		addOptionS(OptionBuilder.withLongOpt(Configuration.HELP_OPTION).withDescription("Print this help message.").create("h"));
		addOptionS(OptionBuilder.withLongOpt(Configuration.VERSION_OPTION).withDescription("Print version information.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.VERBOSE_OPTION).withDescription("Verbose output.").create("v"));

		addOptionS(OptionBuilder.withLongOpt(Configuration.PROGRAMS_OPTION).hasArg().withArgName("dir").withDescription("Programs directory in single job mode, or a root directory for programs in batch mode. By default this is the directory where <file> reside.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.EXTENSIONS_OPTION).hasArg().withArgName("string").withDescription("The list of program extensions separated by whitespaces. Required in single job mode, invalid in batch mode.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.EXCLUDE_OPTION).hasArg().withArgName("file").withDescription("The list of programs which will not be tested. Valid only in single job mode.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.RESULTS_OPTION).hasArg().withArgName("dir").withDescription("Directory containing input and expected output for programs in single job mode, or a root directory for the expected I/O for programs in batch mode. By default this is the directory where <file> reside.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.SKIP_OPTION).hasArg().withArgName("steps").withDescription("The list of steps separated by whitespace to be skipped. A step is either [" + Configuration.KOMPILE_STEP + "|" + Configuration.PDF_STEP + "|" + Configuration.PROGRAMS_STEP + "].").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.DIRECTORY_OPTION).hasArg().withArgName("dir").withDescription("A root directory where K definitions reside. By default this is the current directory. Valid only in batch mode.").create("d"));
		addOptionS(OptionBuilder.withLongOpt(Configuration.REPORT_OPTION).withDescription("Generate a junit-like report.").create());
		addOptionS(OptionBuilder.withLongOpt(Configuration.PROCESSES_OPTION).hasArg().withArgName("num").withDescription("The maximum number of threads.").create());
        addOptionS(OptionBuilder.withLongOpt(Configuration.TIMEOUT_OPTION).hasArg().withArgName("num").withDescription("The testing time limit (seconds).").create());

		addOptionE(OptionBuilder.withLongOpt("config").withDescription("Just for backward compatibility.").create());
		addOptionE(OptionBuilder.withLongOpt("dry").withDescription("Dry run: print out the commend to be executed without actual execution.").create());
		addOptionE(OptionBuilder.withLongOpt("debug").withDescription("Debugging information.").create());
		addOptionE(OptionBuilder.withLongOpt("ignore-white-spaces").hasArg().withArgName("on|off").withDescription("Ignore white spaces when comparsing results. (Default: on).").create());
		addOptionE(OptionBuilder.withLongOpt("ignore-balanced-parentheses").hasArg().withArgName("on|off").withDescription("Ignore balanced parentheses when comparsing results. (Default: on).").create());
	}
	
	// parse the command line arguments
	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new ActualPosixParser();
		try {
			return parser.parse(options, cmd);
		} catch (ParseException e) {
			org.kframework.utils.Error.silentReport(e.getLocalizedMessage());
		}

		//helpExit(help, Configuration.KTEST, options);
		return null;
	}

	public Options getOptionsStandard() {
		return optionsStandard;
	}
	public Options getOptionsExperimental() {
		return optionsExperimental;
	}
	public ArrayList<Option> getOptionList() {
		return optionList;
	}
}

// vim: noexpandtab
