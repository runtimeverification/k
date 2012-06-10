package main;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

public class KompileOptionsParser {
	Options options;
	HelpFormatter help;

	public KompileOptionsParser() {
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

		Option tempDisamb = new Option("tempDisamb", "tempDisamb", false, "temporary to test the java disambiguator");

		// verbose and help
		OptionGroup nofile = new OptionGroup();
		Option nofileopt = new Option("nofile", "nofilename", false, "don't include the long filenames in the XML.");
		nofile.addOption(nofileopt);

		// latex
		OptionGroup tex = new OptionGroup();
		Option pdf = new Option("pdf", false, "generate pdf from definition");
		Option latex = new Option("latex", false, "generate latex from definition");
		Option maudify = new Option("m", "maudify", false, "maudify the definition");
		Option compile = new Option("c", "compile", false, "compile the definition");
		Option tempcompile = new Option("tempc", "tempce", false, "test new implementation");

		tex.addOption(latex);
		tex.addOption(pdf);
		tex.addOption(compile);
		tex.addOption(tempcompile);
		tex.addOption(maudify);

		OptionGroup warn = new OptionGroup();
		Option warnings = new Option("w", "warnings", false, "display warnings");
		warn.addOption(warnings);

		// xml
		OptionGroup xml = new OptionGroup();
		Option toXml = new Option("xml", false, "generate xml from definition");
		Option fromXml = new Option("fromxml", true, "load definition from xml");

		xml.addOption(toXml);
		xml.addOption(fromXml);

		// language module name
		OptionGroup langGroup = new OptionGroup();
		Option lang = new Option("l", "lang", true, "start module");
		langGroup.addOption(lang);

		// language module name
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
		options.addOptionGroup(warn);
		options.addOptionGroup(xml);
		options.addOptionGroup(libGroup);
		options.addOptionGroup(nofile);
		options.addOption(tempDisamb);
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

		k.utils.Error.helpExit(help, options);
		return null;
	}

	public Options getOptions() {
		return options;
	}

	public HelpFormatter getHelp() {
		return help;
	}
}
