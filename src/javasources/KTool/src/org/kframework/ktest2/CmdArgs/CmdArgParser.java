package org.kframework.ktest2.CmdArgs;

import org.apache.commons.cli.*;

public class CmdArgParser {

    public final Options options;
    public final CommandLine cmdOpts;

    @SuppressWarnings("AccessStaticViaInstance")
    public CmdArgParser(String[] args) throws ParseException {
        options = new Options();

        options.addOption(OptionBuilder.withLongOpt(Constants.HELP_OPTION).withDescription("Print" +
                " this help message.").create("h"));
        options.addOption(OptionBuilder.withLongOpt(Constants.VERSION_OPTION).withDescription
                ("Print version information.").create());

        options.addOption(OptionBuilder.withLongOpt(Constants.VERBOSE_OPTION).withDescription
                ("Verbose output.").create("v"));

        options.addOption(OptionBuilder.withLongOpt(Constants.PROGRAMS_OPTION).hasArg().withArgName
                ("dir").withDescription("Programs directory in single job mode, " +
                "or a root directory for programs in batch mode. By default this is the directory" +
                " where <file> reside.").create());
        options.addOption(OptionBuilder.withLongOpt(Constants.EXTENSIONS_OPTION).hasArg()
                .withArgName("string").withDescription("The list of program extensions separated " +
                        "by whitespaces. Required in single job mode, invalid in batch mode.")
                .create());
        options.addOption(OptionBuilder.withLongOpt(Constants.EXCLUDE_OPTION).hasArg().withArgName
                ("file").withDescription("The list of programs which will not be tested. Valid " +
                "only in single job mode.").create());
        options.addOption(OptionBuilder.withLongOpt(Constants.RESULTS_OPTION).hasArg().withArgName
                ("dir").withDescription("Directory containing input and expected output for " +
                "programs in single job mode, or a root directory for the expected I/O for " +
                "programs in batch mode. By default this is the directory where <file> reside.")
                .create());
        options.addOption(OptionBuilder.withLongOpt(Constants.SKIP_OPTION).hasArg().withArgName
                ("steps")
                .withDescription("The list of steps separated by whitespace to be skipped. A step" +
                        " is either [" + Constants.KOMPILE_STEP + "|" + Constants.PDF_STEP +
                        "|" + Constants.KRUN_STEP + "].").create());
        options.addOption(OptionBuilder.withLongOpt(Constants.DIRECTORY_OPTION).hasArg()
                .withArgName("dir").withDescription("A root directory where K definitions reside." +
                        " By default this is the current directory. Valid only in batch mode.")
                .create("d"));
        options.addOption(OptionBuilder.withLongOpt(Constants.REPORT_OPTION).withDescription
                ("Generate a junit-like report.").create());
        options.addOption(OptionBuilder.withLongOpt(Constants.TIMEOUT_OPTION).hasArg().withArgName
                ("num").withDescription("Time limit for a test case (seconds). Default is 5000 " +
                "seconds.").create());

        cmdOpts = new PosixParser().parse(options, args);
    }
}
