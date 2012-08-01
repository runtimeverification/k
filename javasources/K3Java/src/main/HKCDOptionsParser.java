package main;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

/// Options for Haskell K compiler dump tool
public class HKCDOptionsParser {

	Options options;
	HelpFormatter help;

	public HKCDOptionsParser() {
		options = new Options();
		help = new HelpFormatter();

		// main options
		OptionGroup main = new OptionGroup();
		Option def = new Option("def", "definition", true, "language definition");
		Option pgm = new Option("pgm", "program", true, "the program to parse");
		main.addOption(def);
		main.addOption(pgm);

		// verbose and help
		OptionGroup verb = new OptionGroup();
		Option help = new Option("h", "help", false, "prints this message and exits");
		Option verbose = new Option("v", "verbose", false, "verbose mode");
		verb.addOption(help);
		verb.addOption(verbose);

		options.addOptionGroup(main);
		options.addOptionGroup(verb);
	}

	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new PosixParser();
		try {
			CommandLine cl = parser.parse(options, cmd);
			return cl;
		} catch (ParseException e) {
			k.utils.Error.silentReport(e.getLocalizedMessage());
			e.printStackTrace();
		}

		k.utils.Error.helpExit(help, "hkcd", options);
		return null;
	}

	public Options getOptions() {
		return options;
	}
	
	public HelpFormatter getHelp() {
		return help;
	}
}
