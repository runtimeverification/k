package org.kframework.kcheck;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.kframework.utils.ActualPosixParser;

public class KCheckOptionsParser {
		Options options;
		HelpFormatter help;

		public KCheckOptionsParser() {
			options = new Options();
			help = new HelpFormatter();

			// main options
			OptionGroup main = new OptionGroup();
			Option def = new Option("def", "definition", true, "main file to kompile");
			Option rl = new Option("rlfile", "reachability-rules", true, "file containing reachability rules");
			main.addOption(def);
			main.addOption(rl);

			// program for loading configuration
			OptionGroup pgmG = new OptionGroup();
			Option pgm = new Option("p", "pgm", true, "program file used to build the initial configuration ");
			pgmG.addOption(pgm);
			
			// help option
			OptionGroup verb = new OptionGroup();
			Option help = new Option("h", "help", false, "prints this message and exits");
			Option verbose = new Option("v", "verbose", false, "verbose mode");
			verb.addOption(help);
			verb.addOption(verbose);
			
			OptionGroup simplify = new OptionGroup();
			Option sim = new Option("simplify", false, "simplify the path condition before sending it to SMT solver");
			simplify.addOption(sim);
			
			options.addOptionGroup(main);
			options.addOptionGroup(verb);
			options.addOptionGroup(simplify);
			options.addOptionGroup(pgmG);
		}

		public CommandLine parse(String[] cmd) {
			CommandLineParser parser = new ActualPosixParser();
			try {
				CommandLine cl = parser.parse(options, cmd);
				return cl;
			} catch (ParseException e) {
				org.kframework.utils.Error.silentReport(e.getLocalizedMessage());
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
