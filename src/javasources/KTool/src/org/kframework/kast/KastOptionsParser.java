// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.kast;

import org.apache.commons.cli.*;
import org.kframework.utils.ActualPosixParser;

import java.util.ArrayList;
import java.util.Comparator;

public class KastOptionsParser {

    Options options;
    HelpFormatter help;
    // For printing help messages: options = optionsStandard + optionsExperimental
    private Options optionsStandard;
    private Options optionsExperimental;
    private ArrayList<Option> optionList = new ArrayList<Option>();

    // wrapper function to add an option
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
    // add a standard option
    private void addOptionS(Option opt) {
        addOptionWrapper(opt, true);
    }
    // add an experimental option
    private void addOptionE(Option opt) {
        addOptionWrapper(opt, false);
    }

    public KastOptionsParser() {
        options = new Options();
        help = new HelpFormatter();
        optionsStandard = new Options();
        optionsExperimental = new Options();

        addOptionS(OptionBuilder.withLongOpt("help").withDescription("Print this help message.").create("h"));
        addOptionS(OptionBuilder.withLongOpt("version").withDescription("Print version information.").create());
        addOptionS(OptionBuilder.withLongOpt("verbose").withDescription("Verbose output.").create("v"));

        addOptionS(OptionBuilder.withLongOpt("directory").hasArg().withArgName("dir").withDescription("Path to the directory in which the kompiled K definition resides. The default is the current directory.").create("d"));
        addOptionS(OptionBuilder.withLongOpt("expression").hasArg().withArgName("string").withDescription("An expression to parse passed on the command line. Note that positional arguments are ignored when this option is given.").create("e"));
        addOptionS(OptionBuilder.withLongOpt("parser").hasArg().withArgName("parser").withDescription("Choose a parser. <parser> is either [program|newprogram|ground|rule|binary]. (Default: program).").create());
        addOptionS(OptionBuilder.withLongOpt("sort").hasArg().withArgName("string").withDescription("The start sort for the default parser. (The default is the sort of $PGM from the configuration.)").create());
        addOptionS(OptionBuilder.withLongOpt("help-experimental").withDescription("Print help on non-standard options.").create("X"));

        addOptionE(OptionBuilder.withLongOpt("fast-kast").withDescription("Using the (experimental) faster C SDF parser.").create());
        addOptionE(OptionBuilder.withLongOpt("pretty").withDescription("Pretty print the output.").create());
        addOptionE(OptionBuilder.withLongOpt("tabsize").hasArg().withArgName("num").withDescription("How many spaces to use for each indentation level.").create());
        addOptionE(OptionBuilder.withLongOpt("max-width").hasArg().withArgName("num").withDescription("Line will be split before <num> chars.").create());
        addOptionE(OptionBuilder.withLongOpt("aux-tabsize").hasArg().withArgName("num").withDescription("How many spaces to indent lines which do not fit into max-width. (Default: 2).").create());
        addOptionE(OptionBuilder.withLongOpt("nextline").withDescription("Force newline before first argument.").create());
    }

    public CommandLine parse(String[] cmd) {
        CommandLineParser parser = new ActualPosixParser();
        try {
            CommandLine cl = parser.parse(options, cmd);
            return cl;
        } catch (ParseException e) {
            org.kframework.utils.Error.silentReport(e.getLocalizedMessage());
            //e.printStackTrace();
        }

        //org.kframework.utils.Error.helpExit(help, options);
        return null;
    }

    public Options getOptions() {
        return options;
    }

    public HelpFormatter getHelp() {
        return help;
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
}
