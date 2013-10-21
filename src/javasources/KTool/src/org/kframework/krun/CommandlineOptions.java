package org.kframework.krun;

import org.apache.commons.cli.*;
import org.kframework.utils.ActualPosixParser;

import java.util.ArrayList;
import java.util.Comparator;

public class CommandlineOptions {

	private Options options;
	private HelpFormatter help;
	private CommandLine cl;
	// For printing help messages: options = optionsStandard + optionsExperimental
	private Options optionsStandard;
	private Options optionsExperimental;
    private ArrayList<Option> optionList = new ArrayList<Option>();

    public CommandlineOptions() {
    	options = new Options();
		help = new HelpFormatter();
		optionsStandard = new Options();
		optionsExperimental = new Options();
		
		if (K.debug || K.guidebug) {
			initializeDebugOptions();
		}
		else {
			initializeKRunOptions();
		}
    }

	// wrapper function to add an option
	private void addOptionWrapper(Option opt, boolean isStandard) {
		// for parsing command-line options
		options.addOption(opt);
		// for printing help messages
		getOptionList().add(opt);
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

    //create options displayed in the krun help
	@SuppressWarnings("static-access")
	public void initializeKRunOptions() {

		addOptionS(OptionBuilder.withLongOpt("help").withDescription("Print this help message.").create("h"));
		addOptionS(OptionBuilder.withLongOpt("version").withDescription("Print version information.").create());
		addOptionS(OptionBuilder.withLongOpt("verbose").withDescription("Verbose output.").create("v"));

		// Common K options
		addOptionS(OptionBuilder.withLongOpt("directory").hasArg().withArgName("dir").withDescription("Path to the directory in which the kompiled K definition resides. The default is the current directory.").create("d"));
		addOptionS(OptionBuilder.withLongOpt("main-module").hasArg().withArgName("name").withDescription("Specify main module in which a program starts to execute. The default is the module specified in the given compiled K definition.").create());
		addOptionS(OptionBuilder.withLongOpt("syntax-module").hasArg().withArgName("name").withDescription("Specify main module for syntax. The default is the module specified in the given compiled K definition.").create());
		addOptionS(OptionBuilder.withLongOpt("io").hasArg().withArgName("[on|off]").withDescription("Use real IO when running the definition. (Default: enabled).").create());
		addOptionS(OptionBuilder.withLongOpt("color").hasArg().withArgName("[on|off|extended]").withDescription("Use colors in output. (Default: on).").create());
        addOptionS(OptionBuilder.withLongOpt("terminal-color").hasArg().withArgName("color-name").withDescription("Background color of the terminal. Cells won't be colored in this color. (Default: black).").create());
		addOptionS(OptionBuilder.withLongOpt("parens").hasArg().withArgName("[greedy|smart]").withDescription("Select the parentheses-insertion algorithm. The default value is 'greedy'. Note that 'smart' can take much longer time to execute.").create());
		addOptionS(OptionBuilder.withLongOpt("parser").hasArg().withArgName("file").withDescription("Command used to parse programs. (Default: kast).").create());
		addOptionS(OptionBuilder.withLongOpt("config-var-parser").hasArg().withArgName("file").withDescription("Command used to parse configuration variables. (Default: kast -e).  See --parser above. Applies to subsequent -c options until another parser is specified with this option.").create());
		addOptionS(OptionBuilder.withLongOpt("config-var").hasArgs(2).withValueSeparator('=').withArgName("name=value").withDescription("Specify values for variables in the configuration.").create("c"));

		// Advanced K options
		addOptionS(OptionBuilder.withLongOpt("search").withDescription("In conjunction with it you can specify 3 options that are optional: pattern (the pattern used for search), bound (the number of desired solutions) and depth (the maximum depth of the search).").create());
		addOptionS(OptionBuilder.withLongOpt("search-final").withDescription("Same as --search but only return final states, even if --depth is provided.").create());
		addOptionS(OptionBuilder.withLongOpt("search-all").withDescription("Same as --search but return all matching states, even if --depth is not provided.").create());
		addOptionS(OptionBuilder.withLongOpt("search-one-step").withDescription("Same as --search but search only one transition step.").create());
		addOptionS(OptionBuilder.withLongOpt("search-one-or-more-steps").withDescription("Same as --search-all but exclude initial state, even if it matches.").create());
		addOptionS(OptionBuilder.withLongOpt("pattern").hasArg().withArgName("string").withDescription("Specify a term and/or side condition that the result of execution or search must match in order to succeed. Return the resulting matches as a list of substitutions. In conjunction with it you can specify other 2 options that are optional: bound (the number of desired solutions) and depth (the maximum depth of the search).").create());
		addOptionS(OptionBuilder.withLongOpt("bound").hasArg().withArgName("num").withDescription("The number of desired solutions for search.").create());
		addOptionS(OptionBuilder.withLongOpt("depth").hasArg().withArgName("num").withDescription("The maximum number of computational steps to execute or search the definition for.").create());
		addOptionS(OptionBuilder.withLongOpt("graph").withDescription("Displays the search graph generated by the last search.").create());
		addOptionS(OptionBuilder.withLongOpt("backend").hasArg().withArgName("backend").withDescription("Specify the krun backend to execute with. <backend> is either [maude|java-symbolic]. (Default: maude).").create());
		addOptionS(OptionBuilder.withLongOpt("help-experimental").withDescription("Print help on non-standard options.").create("X"));

		// Experimental options
		addOptionE(OptionBuilder.withLongOpt("fast-kast").withDescription("Using the (experimental) faster C SDF parser.").create());
		addOptionE(OptionBuilder.withLongOpt("statistics").hasArg().withArgName("[on|off]").withDescription("Print Maude's rewrite statistics. (Default: ...).").create());
		addOptionE(OptionBuilder.withLongOpt("term").hasArg().withArgName("string").withDescription("Input argument will be parsed with the specified parser and used as the sole input to krun.").create());
		addOptionE(OptionBuilder.withLongOpt("maude-cmd").hasArg().withArgName("string").withDescription("Maude command used to execute the definition.").create());

		addOptionE(OptionBuilder.withLongOpt("log-io").hasArg().withArgName("[on|off]").withDescription("Make the IO server create logs. (Default: disabled).").create());
		addOptionE(OptionBuilder.withLongOpt("debug").withDescription("Run an execution in debug mode.").create());
		addOptionE(OptionBuilder.withLongOpt("debug-gui").withDescription("Run an execution in debug mode with graphical interface.").create());
		addOptionE(OptionBuilder.withLongOpt("trace").withDescription("Turn on maude trace.").create());
		addOptionE(OptionBuilder.withLongOpt("profile").withDescription("Turn on maude profiler.").create());
		addOptionE(OptionBuilder.withLongOpt("ltlmc").hasArg().withArgName("file/string").withDescription("Specify the formula for model checking through a file or at commandline.").create());
		addOptionE(OptionBuilder.withLongOpt("prove").hasArg().withArgName("file").withDescription("Prove a set of reachability rules.").create());
		addOptionE(OptionBuilder.withLongOpt("smt").hasArg().withArgName("solver").withDescription("SMT solver to use for checking constraints. <solver> is either [z3|gappa|none]. (Default: z3).").create());
		addOptionE(OptionBuilder.withLongOpt("generate-tests").withDescription("Test programs will be generated along with normal search.").create());

		addOptionE(OptionBuilder.withLongOpt("output").hasArg().withArgName("file").withDescription("Store output in the file instead of displaying it.").create("o"));
		addOptionE(OptionBuilder.withLongOpt("output-mode").hasArg().withArgName("mode").withDescription("How to display Maude results. <mode> is either [pretty|raw|binary|none]. (Default: pretty).").create());
	}

	//create options displayed in the krun debugger help
	@SuppressWarnings("static-access")
	public void initializeDebugOptions() {
		//stepper options
		addOptionS(OptionBuilder.withLongOpt("help").withDescription("Display the available commands").create());
		addOptionS(OptionBuilder.withLongOpt("step").withDescription("Execute one step or multiple steps at one time if you specify a positive integer argument").create());
		addOptionS(OptionBuilder.withLongOpt("step-all").withDescription("Computes all successors in one or more transitions (if you specify a positive integer argument) of the current configuration").create());
		addOptionS(OptionBuilder.withLongOpt("select").hasArg().withArgName("number").withDescription("Selects the current configuration after a search result using step-all command").create());
		addOptionS(OptionBuilder.withLongOpt("show-search-graph").withDescription("Displays the search graph generated by the last search").create());
		addOptionS(OptionBuilder.withLongOpt("show-node").hasArg().withArgName("NODE").withDescription("Displays info about the specified node in the search graph." + K.lineSeparator + "The node is specified by its id indicated as argument of this option").create());
		addOptionS(OptionBuilder.withLongOpt("show-edge").hasArgs(2).withArgName("NODE1 NODE2").withDescription("Displays info about the specifiede edge in the search graph." + K.lineSeparator + "The edge is specified by the ids of the endpoints indicated as argument of this option").create());
		addOptionS(OptionBuilder.withLongOpt("resume").withDescription("Resume the execution and exit from the debug mode").create());
		addOptionS(OptionBuilder.withLongOpt("abort").withDescription("Abort the execution and exit from the debug mode").create());
		addOptionS(OptionBuilder.withLongOpt("save").hasArg().withArgName("STRING").withDescription("Save the debug session to file").create());
		addOptionS(OptionBuilder.withLongOpt("load").hasArg().withArgName("STRING").withDescription("Load the debug session from file").create());
		addOptionS(OptionBuilder.withLongOpt("read").hasArg().withArgName("STRING").withDescription("Read a string from stdin").create());
	}

	public CommandLine parse(String[] cmd) {
		CommandLineParser parser = new ActualPosixParser();
		try {
			setCommandLine(parser.parse(options, cmd));
			return getCommandLine();
		} catch (ParseException e) {
			System.out.println("Error while parsing commandline:" + e.getMessage());
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

	public Options getOptionsStandard() {
		return optionsStandard;
	}
	public Options getOptionsExperimental() {
		return optionsExperimental;
	}

	public ArrayList<Option> getOptionList() {
		return optionList;
	}

	public void setOptionList(ArrayList<Option> optionList) {
		this.optionList = optionList;
	}
	
}
