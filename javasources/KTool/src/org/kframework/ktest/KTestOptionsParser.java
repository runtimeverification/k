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
		
		OptionGroup helpGroup = new OptionGroup();
		Option help = new Option("h", "help", false, "prints this message and exits");
		helpGroup.addOption(help);
		
		OptionGroup configGroup = new OptionGroup();
		Option config = new Option("config",  true, "XML configuration file containing tests");
		configGroup.addOption(config);
		
		OptionGroup verbGroup = new OptionGroup();
		Option version = new Option("version", false, "prints version number");
		verbGroup.addOption(version);
		
		options.addOptionGroup(helpGroup);
		options.addOptionGroup(configGroup);
		options.addOptionGroup(verbGroup);
	}
	
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
	
	public static void helpExit(HelpFormatter help, String cmdLineSyntax, Options options) {
		System.out.println("\n");
		help.printHelp(cmdLineSyntax, "\nTest K definitions and programs.\n\n", options, "\n", true);
		System.out.println("\n");
		System.exit(1);
	}

}
