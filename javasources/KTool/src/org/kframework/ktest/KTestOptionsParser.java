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
		Option help = new Option("h", Configuration.HELP_OPTION, false, "prints this message and exits");
		Option version = new Option(Configuration.VERSION_OPTION, false, "prints version number");
		helpGroup.addOption(help);
		helpGroup.addOption(version);
		
		// configuration file
		OptionGroup configGroup = new OptionGroup();
		Option config = new Option(Configuration.CONFIG_OPTION,  true, "XML configuration file containing tests");
		configGroup.addOption(config);

		// language group
		OptionGroup languageGroup = new OptionGroup();
		Option language = new Option("def", Configuration.LANGUAGE_OPTION, true, "K definition or directory (in case a configuration file is provided)");
		languageGroup.addOption(language);
		
		// programs directory
		OptionGroup programsGroup = new OptionGroup();
		Option programs = new Option(Configuration.PROGRAMS_OPTION, true, "Programs directory");
		programsGroup.addOption(programs);

		// the list of excluded programs
		OptionGroup extensionsGroup = new OptionGroup();
		Option extensions = new Option(Configuration.EXTENSIONS_OPTION, true, "The list of programs which will not be tested");
		extensionsGroup.addOption(extensions);
		
		// the list of excluded programs
		OptionGroup excludeGroup = new OptionGroup();
		Option exclude = new Option(Configuration.EXCLUDE_OPTION, true, "The list of programs which will not be tested");
		excludeGroup.addOption(exclude);

		// the list of excluded programs
		OptionGroup resultsGroup = new OptionGroup();
		Option results = new Option(Configuration.RESULTS_OPTION, true, "Directory containing I/O for programs");
		resultsGroup.addOption(results);
		
		options.addOptionGroup(helpGroup);
		options.addOptionGroup(configGroup);
		options.addOptionGroup(languageGroup);
		options.addOptionGroup(programsGroup);
		options.addOptionGroup(extensionsGroup);
		options.addOptionGroup(excludeGroup);
		options.addOptionGroup(resultsGroup);
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

		helpExit(help, "help", options);
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
		help.printHelp(cmdLineSyntax, "\nTest K definitions and programs.\n\n", options, "\n", true);
		System.out.println("\n");
		System.exit(1);
	}

}
