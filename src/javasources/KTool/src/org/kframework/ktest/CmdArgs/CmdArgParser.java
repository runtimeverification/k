// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.CmdArgs;

import org.apache.commons.cli.*;

import java.util.ArrayList;
import java.util.List;

public class CmdArgParser {

    public final CommandLine cmdOpts;
    private final Options options = new Options();
    private final List<Option> optionList = new ArrayList<Option>();

    @SuppressWarnings("AccessStaticViaInstance")
    public CmdArgParser(String[] args) throws ParseException {
        addOption(OptionBuilder.withLongOpt(Constants.HELP_OPTION)
                .withDescription("Print this help message.").create("h"));
        addOption(OptionBuilder.withLongOpt(Constants.VERSION_OPTION)
                .withDescription("Print version information.").create());

        addOption(OptionBuilder.withLongOpt(Constants.VERBOSE_OPTION)
                .withDescription("Verbose output.").create("v"));

        addOption(OptionBuilder.withLongOpt(Constants.COLOR_SETTING).hasArg()
                .withArgName("[on|off|extended]")
                .withDescription("Use colors in output. (Default: on)").create());

        addOption(OptionBuilder.withLongOpt(Constants.PROGRAMS_OPTION).hasArg()
                .withArgName("dir").withDescription("Programs directory in single job mode, " +
                        "or a root directory for programs in batch mode. By default this is the " +
                        "directory where <file> reside.").create());
        addOption(OptionBuilder.withLongOpt(Constants.EXTENSION_OPTION).hasArg()
                .withArgName("string").withDescription("The list of program extensions separated " +
                        "by whitespaces. Required in single job mode, invalid in batch mode.")
                .create());
        addOption(OptionBuilder.withLongOpt(Constants.EXCLUDE_OPTION).hasArg()
                .withArgName("file").withDescription("The list of programs which will not be " +
                        "tested. Valid only in single job mode.").create());
        addOption(OptionBuilder.withLongOpt(Constants.RESULTS_OPTION).hasArg()
                .withArgName("dir").withDescription("Directory containing input and expected " +
                        "output for programs in single job mode, or a root directory for the " +
                        "expected I/O for programs in batch mode. By default this is the " +
                        "directory where <file> reside.").create());
        addOption(OptionBuilder.withLongOpt(Constants.SKIP_OPTION).hasArg()
                .withArgName("steps")
                .withDescription("The list of steps to be skipped, separated by whitespace. " +
                        "A step is either [" + Constants.KOMPILE_STEP + "|" + Constants.PDF_STEP +
                        "|" + Constants.KRUN_STEP + "].").create());
        addOption(OptionBuilder.withLongOpt(Constants.DIRECTORY_OPTION).hasArg()
                .withArgName("dir").withDescription("A root directory where K definitions reside." +
                        " By default this is the current directory. Valid only in batch mode.")
                .create("d"));
        addOption(OptionBuilder.withLongOpt(Constants.REPORT_OPTION)
                .withDescription("Generate a junit-like report.").create());
        addOption(OptionBuilder.withLongOpt(Constants.TIMEOUT_OPTION).hasArg()
                .withArgName("num").withDescription("Time limit for each process (milliseconds). " +
                        "Default is 300000 milliseconds.").create());
        addOption(OptionBuilder.withLongOpt(Constants.UPDATE_OUT_OPTION)
                .withDescription("Update existing .out files.")
                .create());
        addOption(OptionBuilder.withLongOpt(Constants.GENERATE_OUT_OPTION)
                .withDescription("Newly generate .out files if needed.")
                .create());
        addOption(OptionBuilder.withLongOpt(Constants.THREADS_SETTING).hasArg()
                .withArgName("threads")
                .withDescription("Maximum number of threads spawned for parallel execution.")
                .create());

        addOption(OptionBuilder.withLongOpt(Constants.IGNORE_WS).hasArg().withArgName("on|off")
                .withDescription("Ignore white spaces when comparing results. (Default: on).")
                .create());
        addOption(OptionBuilder.withLongOpt(Constants.IGNORE_B_PARENS).hasArg()
                .withArgName("on|off").withDescription("Ignore balanced parentheses when " +
                        "comparing results. (Default: on).").create());

        addOption(OptionBuilder.withLongOpt(Constants.DRY).withDescription("Dry run: print out the " +
                "command to be executed without actual execution.").create());
        addOption(OptionBuilder.withLongOpt(Constants.DEBUG).withDescription(
                "Run in debugging mode (prints stack traces when uncaught exceptions are thrown)")
                .create());

        cmdOpts = new PosixParser().parse(options, args);
    }

    private void addOption(Option option) {
        options.addOption(option);
        optionList.add(option);
    }

    public List<Option> getOptionList() {
        return optionList;
    }

    public Options getOptions() {
        return options;
    }
}
