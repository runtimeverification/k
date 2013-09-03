package org.kframework.ktest;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.kframework.utils.ActualPosixParser;

public class KTestOptionsParser {

	Options options;
	HelpFormatter help;

	public KTestOptionsParser() {
		options = new Options();
		help = new HelpFormatter();
		
		// Metadata options
		OptionGroup helpGroup = new OptionGroup();
		Option help = new Option("h", Configuration.HELP_OPTION, false, "Prints this message and exits");
		Option version = new Option(Configuration.VERSION_OPTION, false, "Prints version number");
		helpGroup.addOption(help);
		helpGroup.addOption(version);
		
		// configuration file
		OptionGroup configGroup = new OptionGroup();
		Option config = new Option(Configuration.CONFIG_OPTION,  true, "XML configuration file containing tests");
		configGroup.addOption(config);

		// language group
		OptionGroup languageGroup = new OptionGroup();
		Option language = new Option("def", Configuration.LANGUAGE_OPTION, true, "K definition or, in case the -config option is used, a root directory for K definitions");
		languageGroup.addOption(language);
		
		// programs directory
		OptionGroup programsGroup = new OptionGroup();
		Option programs = new Option(Configuration.PROGRAMS_OPTION, true, "Programs directory or, in case the -config option is used, a root directory for programs");
		programsGroup.addOption(programs);

		// the list of excluded programs
		OptionGroup extensionsGroup = new OptionGroup();
		Option extensions = new Option(Configuration.EXTENSIONS_OPTION, true, "The list of program extensions separated by whitespaces");
		extensionsGroup.addOption(extensions);
		
		// the list of excluded programs
		OptionGroup excludeGroup = new OptionGroup();
		Option exclude = new Option(Configuration.EXCLUDE_OPTION, true, "The list of programs which will not be tested");
		excludeGroup.addOption(exclude);

		// the list of excluded programs
		OptionGroup resultsGroup = new OptionGroup();
		Option results = new Option(Configuration.RESULTS_OPTION, true, "Directory containing I/O for programs or, in case the -config option is used, a root directory for the I/O for programs");
		resultsGroup.addOption(results);
		
		// --skip
		OptionGroup skipGroup = new OptionGroup();
		Option skip = new Option(Configuration.SKIP_OPTION, true, "The list of steps separated by whitespace to be skipped (" + Configuration.KOMPILE_STEP + "/" + Configuration.PDF_STEP + "/" + Configuration.PROGRAMS_STEP + ")");
		skipGroup.addOption(skip);
		
		// --verbose
		OptionGroup vGroup = new OptionGroup();
		Option verbose = new Option("v",  Configuration.VERBOSE_OPTION, false, "Verbose mode");
		vGroup.addOption(verbose);
		
		// add all option groups to ktest options
		options.addOptionGroup(helpGroup);
		options.addOptionGroup(configGroup);
		options.addOptionGroup(languageGroup);
		options.addOptionGroup(programsGroup);
		options.addOptionGroup(extensionsGroup);
		options.addOptionGroup(excludeGroup);
		options.addOptionGroup(resultsGroup);
		options.addOptionGroup(skipGroup);
		options.addOptionGroup(vGroup);
	}
	
	// parse the command line arguments
	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new ActualPosixParser();
		try {
			CommandLine cl = parser.parse(options, cmd);
			return cl;
		} catch (ParseException e) {
			org.kframework.utils.Error.silentReport(e.getLocalizedMessage());
			e.printStackTrace();
		}

		helpExit(help, Configuration.KTEST, options);
		return null;
	}

	public Options getOptions() {
		return options;
	}

	public HelpFormatter getHelp() {
		return help;
	}	
	
	// prints the header of help message and exits with an error code
	public static void helpExit(HelpFormatter help, String cmdLineSyntax, Options options) {
		System.out.println("\n");
		help.printHelp(79, cmdLineSyntax, "\nTest K definitions and programs.\n\n", options, Configuration.DETAILED_HELP_MESSAGE, true);
		System.out.println("\n");
		System.exit(1);
	}

}
