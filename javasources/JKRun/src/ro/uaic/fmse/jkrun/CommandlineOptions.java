package ro.uaic.fmse.jkrun;

import java.util.ArrayList;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

public class CommandlineOptions {

	Options options;
	HelpFormatter help;
	private CommandLine cl;
    public static ArrayList<Option> optionList = new ArrayList<Option>();
	
	public CommandlineOptions() {
		options = new Options();
		help = new HelpFormatter();

		// General options
		Option help1 = new Option("h", "help", false, "Display the detailed help message and quit");
		Option help2 = new Option("?", false, "Display the detailed help message and quit");
		Option version = new Option("v", "version", false, "Display the version number and quit");
		Option desk_file = OptionBuilder.hasArg(true).withArgName("FILE").withLongOpt("desk-file").withDescription("Set Desk file path, instead of searching for it").create();

		options.addOption(help1); optionList.add(help1);
		options.addOption(help2); optionList.add(help2);
		options.addOption(version); optionList.add(version);
		options.addOption(desk_file); optionList.add(desk_file);

		// Common K options
		Option pgm = OptionBuilder.hasArg(true).withArgName("FILE").withLongOpt("pgm").withDescription("Name of the program to execute").create();
		Option k_definition = OptionBuilder.hasArg(true).withArgName("FILE").withLongOpt("k-definition").withDescription("Path to the K definition").create();
		Option main_module = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("main-module").withDescription("Module the program should execute in").create();
		Option syntax_module = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("syntax-module").withDescription("Name of the syntax module").create();
		Option parser = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("parser").withDescription("Command used to parse programs (default: kast)").create();
		Option io = OptionBuilder.hasArg(false).withLongOpt("io").withDescription("Use real IO when running the definition").create();
		Option no_io = OptionBuilder.hasArg(false).withLongOpt("no-io").create();
		Option statistics = OptionBuilder.hasArg(false).withLongOpt("statistics").withDescription("Print Maude's rewrite statistics").create();
		Option no_statistics = OptionBuilder.hasArg(false).withLongOpt("no-statistics").create();
		Option color = OptionBuilder.hasArg(false).withLongOpt("color").withDescription("Use colors in output").create();
		Option no_color = OptionBuilder.hasArg(false).withLongOpt("no-color").create();
		Option parens = OptionBuilder.hasArg(false).withLongOpt("parens").withDescription("Show parentheses in output").create();
		Option no_parens = OptionBuilder.hasArg(false).withLongOpt("no-parens").create();

		options.addOption(pgm); optionList.add(pgm);
		options.addOption(k_definition); optionList.add(k_definition);
		options.addOption(main_module); optionList.add(main_module);
		options.addOption(syntax_module); optionList.add(syntax_module);
		options.addOption(parser); optionList.add(parser);
		options.addOption(io); optionList.add(io);
		options.addOption(no_io); optionList.add(no_io);
		options.addOption(statistics); optionList.add(statistics);
		options.addOption(no_statistics); optionList.add(no_statistics);
		options.addOption(color); optionList.add(color);
		options.addOption(no_color); optionList.add(no_color);
		options.addOption(parens); optionList.add(parens);
		options.addOption(no_parens); optionList.add(no_parens);

		// Advanced K options
		Option compiled_def = OptionBuilder.hasArg(true).withArgName("FILE").withLongOpt("compiled-def").withDescription("Path to the compiled K definition").create();
		Option do_search = OptionBuilder.hasArg(false).withLongOpt("do-search").withDescription("Search for all possible results").create();
		Option no_do_search = OptionBuilder.hasArg(false).withLongOpt("no-do-search").create();
		Option maude_cmd = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("maude-cmd").withDescription("Maude command used to execute the definition").create();
		Option xsearch_pattern = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("xsearch-pattern").withDescription("Search pattern").create();
		Option output_mode = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("output-mode").withDescription("How to display Maude results (none, raw, pretty)").create();
		Option log_io = OptionBuilder.hasArg(false).withLongOpt("log-io").withDescription("Tell the IO server to create logs").create();
		Option no_log_io = OptionBuilder.hasArg(false).withLongOpt("no-log-io").create();

		options.addOption(compiled_def); optionList.add(compiled_def);
		options.addOption(do_search); optionList.add(do_search);
		options.addOption(no_do_search); optionList.add(no_do_search);
		options.addOption(maude_cmd); optionList.add(maude_cmd);
		options.addOption(xsearch_pattern); optionList.add(xsearch_pattern);
		options.addOption(output_mode); optionList.add(output_mode);
		options.addOption(log_io); optionList.add(log_io);
		options.addOption(no_log_io); optionList.add(no_log_io);

		// for debugger
		Option debug = OptionBuilder.hasArg(false).withLongOpt("debug").withDescription("Run an execution in debug mode").create();
		Option rule_labels = OptionBuilder.hasArg(true).withArgName("STRING").withLongOpt("rule-labels").withDescription("A list of labels associated to rules for breakpoint execution").create();

		options.addOption(debug); optionList.add(debug);
		options.addOption(rule_labels); optionList.add(rule_labels);

	}

	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new PosixParser();
		try {
			setCommandLine(parser.parse(options, cmd));
			return getCommandLine();
		} catch (ParseException e) {
			e.printStackTrace();
		}

		return null;
	}

	public Options getOptions() {
		return options;
	}

	public HelpFormatter getHelp() {
		return help;
	}

	CommandLine getCommandLine() {
		return cl;
	}

	void setCommandLine(CommandLine cl) {
		this.cl = cl;
	}
	
	
	
}