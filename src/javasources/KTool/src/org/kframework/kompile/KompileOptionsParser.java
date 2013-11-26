package org.kframework.kompile;

import org.apache.commons.cli.*;
import org.kframework.utils.ActualPosixParser;

import java.util.ArrayList;

public class KompileOptionsParser {

	private final Options options;
	private final HelpFormatter help;
	// For printing help messages: options = optionsStandard + optionsExperimental
	private final Options optionsStandard;
	private final Options optionsExperimental;
	private final ArrayList<Option> optionList = new ArrayList<>();

    public KompileOptionsParser() {
        options = new Options();
        help = new HelpFormatter();
        optionsStandard = new Options();
        optionsExperimental = new Options();

        addOptionS(OptionBuilder.withLongOpt("help").withDescription("Print this help message.").create("h"));
        addOptionS(OptionBuilder.withLongOpt("version").withDescription("Print version information.").create());
        addOptionS(OptionBuilder.withLongOpt("verbose").withDescription("Verbose output.").create("v"));

        // Common options
        addOptionS(OptionBuilder.withLongOpt("directory").hasArg().withArgName("dir").withDescription("Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the current directory.").create("d"));
        addOptionS(OptionBuilder.withLongOpt("backend").hasArg().withArgName("backend").withDescription("Choose a backend. <backend> is one of [pdf|latex|html|maude|java|unparse|symbolic]. Each of [pdf|latex|html] generates a document from the given K definition. Either of [maude|java] creates the kompiled K definition. 'unparse' generates an unparsed version of the given K definition. 'symbolic' generates symbolic semantics.").create());
        addOptionS(OptionBuilder.withLongOpt("doc-style").hasArg().withArgName("string/file").withDescription("Specify a style option for the package 'k.sty' (when '--backend [pdf|latex]' is used) or path to an alternative .css file (when '--backend html' is used).").create());
        addOptionS(OptionBuilder.withLongOpt("warnings").hasArg().withArgName("all|none").withDescription("Warning level. (Default: none).").create("w"));
        addOptionS(OptionBuilder.withLongOpt("main-module").hasArg().withArgName("string").withDescription("Specify main module in which a program starts to execute. This information is used by 'krun'. The default is the name of the given K definition file without the extension (.k).").create());
        addOptionS(OptionBuilder.withLongOpt("syntax-module").hasArg().withArgName("string").withDescription("Specify main module for syntax. This information is used by 'krun'. (Default: <main-module>-SYNTAX).").create());

        // Advanced options
        addOptionS(OptionBuilder.withLongOpt("superheat").hasArg().withArgName("string").withDescription("Specifies which syntactic constructs superheat the computation. To be used in combination with --supercool. <string> is a space-separated list of production tags.").create());
        addOptionS(OptionBuilder.withLongOpt("supercool").hasArg().withArgName("string").withDescription("Specifies which rules supercool the computation. To be used in combination with --superheat. <string> is a space-separated list of rule tags.").create());
        addOptionS(OptionBuilder.withLongOpt("transition").hasArg().withArgName("string").withDescription("<string> is a space-separated list of tags designating rules to become transitions.").create());
        addOptionS(OptionBuilder.withLongOpt("help-experimental").withDescription("Print help on non-standard options.").create("X"));

        // Experimental options
        addOptionE(OptionBuilder.withLongOpt("step").hasArg().withArgName("string").withDescription("Name of the compilation phase after which the compilation process should stop.").create());
        addOptionE(OptionBuilder.withLongOpt("lib").hasArg().withArgName("file").withDescription("Specify extra-libraries for compile/runtime.").create());
        addOptionE(OptionBuilder.withLongOpt("add-top-cell").withDescription("Add a top cell to configuration and all rules.").create());
        addOptionE(OptionBuilder.withLongOpt("kcells").hasArg().withArgName("string").withDescription("Cells which contain komputations.").create());
        addOptionE(OptionBuilder.withLongOpt("sort-cells").withDescription("Sort cells according to the order in the configuration.").create());
        addOptionE(OptionBuilder.withLongOpt("smt").hasArg().withArgName("solver").withDescription("SMT solver to use for checking constraints. <solver> is one of [z3|none]. (Default: z3). This only has an effect with '--backend symbolic'.").create());
        addOptionE(OptionBuilder.withLongOpt("fast-kast").withDescription("Using the (experimental) faster C SDF parser.").create());
        addOptionE(OptionBuilder.withLongOpt("symbolic-rules").hasArg().withArgName("tags").withDescription("Apply symbolic transformations only to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.").create());
        addOptionE(OptionBuilder.withLongOpt("non-symbolic-rules").hasArg().withArgName("tags").withDescription("Do not apply symbolic transformations to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.").create());
        addOptionE(OptionBuilder.withLongOpt("concrete-sort").withDescription("Use concrete sorts when generating heating and cooling rules.").create());

        addOptionE(OptionBuilder.withLongOpt("loud").withDescription("Prints 'Done' at the end if all is ok.").create());
    }

    public CommandLine parse(String[] cmd) {
        CommandLineParser parser = new ActualPosixParser();
        try {
            CommandLine cl = parser.parse(options, cmd);
            return cl;
        } catch (ParseException e) {
            org.kframework.utils.Error.report(e.getLocalizedMessage());
        }
        return null; // unreachable code
    }

	Options getOptions() {
		return options;
	}

	HelpFormatter getHelp() {
		return help;
	}

	Options getOptionsStandard() {
		return optionsStandard;
	}

	Options getOptionsExperimental() {
		return optionsExperimental;
	}

	ArrayList<Option> getOptionList() {
		return optionList;
	}

    private void addOptionWrapper(Option opt, boolean isStandard) {
        // for parsing command-line options
        options.addOption(opt);
        // for printing help messages
        optionList.add(opt);
        if (isStandard) {
            optionsStandard.addOption(opt);
        } else {
            optionsExperimental.addOption(opt);
        }
    }

    private void addOptionS(Option opt) {
        addOptionWrapper(opt, true);
    }

    private void addOptionE(Option opt) {
        addOptionWrapper(opt, false);
    }
}
