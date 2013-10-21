package org.kframework.main;

import org.apache.commons.cli.*;
import org.kframework.utils.ActualPosixParser;

public class OptionsParser {

	Options options;
	HelpFormatter help;

	public OptionsParser() {
		options = new Options();
		help = new HelpFormatter();

		// main options
		OptionGroup main = new OptionGroup();
		Option def = new Option("def", "definition", true, "main file to kompile");
		main.addOption(def);

		// verbose and help
		OptionGroup verb = new OptionGroup();
		Option help = new Option("h", "help", false, "prints this message and exits");
		Option verbose = new Option("v", "verbose", false, "verbose mode");
		verb.addOption(help);
		verb.addOption(verbose);

		// verbose and help
		OptionGroup nofile = new OptionGroup();
		Option nofileopt = new Option("nofile", "nofilename", false, "don't include the long filenames in the XML.");
		nofile.addOption(nofileopt);

		// latex
		OptionGroup tex = new OptionGroup();
		// Option pdf = new Option("pdf", false, "generate pdf from definition");
		// Option latex = new Option("latex", false, "generate latex from definition");
		Option maudify = new Option("m", "maudify", false, "maudify the definition");
		Option compile = new Option("c", "compile", false, "compile the definition");
		Option parse = new Option("kast", "kast", false, "parse a program");

		// tex.addOption(latex);
		// tex.addOption(pdf);
		tex.addOption(compile);
		tex.addOption(maudify);
		tex.addOption(parse);

		OptionGroup tex2 = new OptionGroup();
		Option tbl = new Option("pgm", "program", true, "the program to parse");
		tex2.addOption(tbl);

		//language module name
		OptionGroup langGroup = new OptionGroup();
		Option lang = new Option("l", "lang", true, "start module");
		langGroup.addOption(lang);

		//language module name
		OptionGroup langSynGroup = new OptionGroup();
		Option langSyn = new Option("synmod", "syntax-module", true, "start module for syntax");
		langSynGroup.addOption(langSyn);

		// language module name
		// OptionGroup preludeGroup = new OptionGroup();
		// Option prelude = new Option("prelude", true, "Load a different prelude file.");
		// preludeGroup.addOption(prelude);

		 // lib
		 OptionGroup libGroup = new OptionGroup();
		 Option lib = new Option("lib", true, "Specify extra-libraries for compile/runtime.");
		 libGroup.addOption(lib);

		// add options
		options.addOptionGroup(verb);
		options.addOptionGroup(main);
		options.addOptionGroup(langGroup);
		options.addOptionGroup(langSynGroup);
		options.addOptionGroup(tex);
		options.addOptionGroup(tex2);
		options.addOptionGroup(libGroup);
		options.addOptionGroup(nofile);
	}

	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new ActualPosixParser();
		try {
			CommandLine cl = parser.parse(options, cmd);
			if (cl.getOptions().length > 0)
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
