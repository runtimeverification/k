package org.kframework.main;

import org.apache.commons.cli.*;

public class KastOptionsParser {

	Options options;
	HelpFormatter help;

	public KastOptionsParser() {
		options = new Options();
		help = new HelpFormatter();

		// main options
		OptionGroup main = new OptionGroup();
		Option def = new Option("def", "definition", true, "main file of the definition");
		main.addOption(def);

		// verbose and help
		OptionGroup verb = new OptionGroup();
		Option help = new Option("h", "help", false, "prints this message and exits");
		Option version = new Option("version", false, "prints version number");
		Option verbose = new Option("v", "verbose", false, "verbose mode");
		verb.addOption(help);
		verb.addOption(version);
		verb.addOption(verbose);

		// no filename
		OptionGroup nofile = new OptionGroup();
		Option nofileopt = new Option("nofile", "nofilename", false, "don't include the long filenames in the XML.");
		nofile.addOption(nofileopt);

		/// program
		OptionGroup tex2 = new OptionGroup();
		Option tbl = new Option("pgm", "program", true, "the program to parse");
		Option exp = new Option("e", "expression", true, "an expression to parse passed on the command line");
		tex2.addOption(tbl);
		tex2.addOption(exp);

		// indentation options
		Option prettyPrint = new Option("pretty", false, "pretty print the output");
		Option tabSize = new Option("tabsize", true, "how many spaces to use for each indentation level");
		Option maxWidth = new Option("maxwidth", true, "the indicative maximal width of the output");
		Option auxSize = new Option("auxtabsize", true, "how many spaces to indent lines which do not fit into max-width");
		Option nextLine = new Option("nextline", false, "force newline before first argument");
		
		// which parser to use
		@SuppressWarnings("static-access")
		Option defParser = OptionBuilder.withLongOpt("def-parser").withDescription("use k definition parser").create();
		@SuppressWarnings("static-access")
		Option sort = OptionBuilder.withLongOpt("sort").hasArg().withDescription("the sort the program is expected to parse into").create();

		// add options
		options.addOptionGroup(verb);
		options.addOptionGroup(main);
		options.addOptionGroup(tex2);
		options.addOptionGroup(nofile);
		options.addOption(prettyPrint);
		options.addOption(tabSize);
		options.addOption(maxWidth);
		options.addOption(auxSize);
		options.addOption(nextLine);
		options.addOption(defParser);
		options.addOption(sort);
	}

	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new PosixParser();
		try {
			CommandLine cl = parser.parse(options, cmd);
			return cl;
		} catch (ParseException e) {
			org.kframework.utils.Error.silentReport(e.getLocalizedMessage());
			e.printStackTrace();
		}

		org.kframework.utils.Error.helpExit(help, options);
		return null;
	}

	public Options getOptions() {
		return options;
	}

	public HelpFormatter getHelp() {
		return help;
	}
}
