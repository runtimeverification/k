// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.CmdArgs;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.io.FilenameUtils;
import org.kframework.krun.ColorSetting;
import org.kframework.ktest.IgnoringStringMatcher;
import org.kframework.ktest.KTestStep;
import org.kframework.ktest.StringMatcher;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents valid command line arguments. This class can only be instantiated using
 * `validateArgs' method, which ensures validation of arguments.
 *
 * Being valid means:
 *   - File paths are valid(e.g. point to a files/directories) relative to current directory
 *   - Only one unnamed argument is passed
 *   - File extension is either .k or .xml
 */
public class CmdArg {

    /**
     * A root directory where K definitions reside. By default this is the current directory.
     * Valid only in batch mode.
     */
    private String directory;

    /**
     * Programs directory in single job mode, or a root directory for programs in batch mode. By
     * default this is the directory where <file> reside.
     */
    private String programs;

    /**
     * Directory containing input and expected output for programs in single job mode,
     * or a root directory for the expected I/O for programs in batch mode. By default this is
     * the directory where <file> reside.
     */
    private String results;

    /**
     * The list of program extensions separated by whitespaces. Required in single job mode,
     * invalid in batch mode.
     */
    private final String[] extensions;

    /**
     * The list of programs which will not be tested. Valid only in single job mode.
     */
    private final String[] excludes;

    /**
     * The list of steps separated by whitespace to be skipped.
     */
    private final Set<KTestStep> skips;

    /**
     * Maximum number of threads spawned for parallel execution.
     */
    private final int threads;

    /**
     * Generate a junit-like report.
     */
    private final boolean generateReport;

    /**
     * Config XML file for batch mode, K definition for single job mode.
     */
    private String targetFile;

    /**
     * Enable verbose output.
     */
    private final boolean verbose;

    /**
     * Colorful output settings.
     */
    private final ColorSetting colorSetting;

    /**
     * Timeout for processes spawned by ktest. (in seconds)
     */
    private final int timeout;

    /**
     * Update existing .out files.
     */
    private final boolean updateOut;

    /**
     * Newly generate .out files if needed.
     */
    private final boolean generateOut;

    /**
     * Ignore whitespace while comparing program outputs.
     */
    private final boolean ignoreWS;

    /**
     * Ignore balanced parens while comparing program outputs.
     */
    private final boolean ignoreBalancedParens;

    /**
     * Dry run.
     */
    private final boolean dry;

    /**
     * Run in debugging mode. (prints stack traces when uncaught exceptions are thrown)
     */
    private final boolean debug;

    private CmdArg(String directory, String programs, String results, String[] extensions,
                   String[] excludes, Set<KTestStep> skips, int threads, boolean generateReport,
                   String targetFile, boolean verbose, ColorSetting colorSetting, int timeout,
                   boolean updateOut, boolean generateOut,
                   boolean ignoreWS, boolean ignoreBalancedParens, boolean dry, boolean debug) {
        this.directory = directory;
        this.programs = programs;
        this.results = results;
        this.extensions = extensions;
        this.excludes = excludes;
        this.skips = skips;
        this.threads = threads;
        this.generateReport = generateReport;
        this.targetFile = targetFile;
        this.verbose = verbose;
        this.colorSetting = colorSetting;
        this.timeout = timeout;
        this.updateOut = updateOut;
        this.generateOut = generateOut;
        this.ignoreWS = ignoreWS;
        this.ignoreBalancedParens = ignoreBalancedParens;
        this.dry = dry;
        this.debug = debug;
    }

    /**
     * Copy constructor.
     * @param obj CmdArg object to copy
     */
    public CmdArg(CmdArg obj) {
        this.directory = obj.directory;
        this.programs = obj.programs;
        this.results = obj.results;
        this.extensions = obj.extensions;
        this.excludes = obj.excludes;
        this.skips = obj.skips;
        this.threads = obj.threads;
        this.generateReport = obj.generateReport;
        this.targetFile = obj.targetFile;
        this.verbose = obj.verbose;
        this.colorSetting = obj.colorSetting;
        this.timeout = obj.timeout;
        this.updateOut = obj.updateOut;
        this.generateOut = obj.generateOut;
        this.ignoreWS = obj.ignoreWS;
        this.ignoreBalancedParens = obj.ignoreBalancedParens;
        this.dry = obj.dry;
        this.debug = obj.debug;
    }

    /**
     * Validate raw data parsed from command line arguments and return CmdArg objects,
     * which is needed for TestSuite to run tests.
     * @param cmdOpts CommandLine object generated by command line argument parser
     * @return validated CmdArg object that is needed by TestSuite
     * @throws InvalidArgumentException in case of an invalid argument
     */
    public static CmdArg validateArgs(CommandLine cmdOpts) throws InvalidArgumentException {
        String currentDir = System.getProperty("user.dir");
        String[] args = cmdOpts.getArgs();

        if (args.length != 1)
            throw new InvalidArgumentException("ktest requires exactly one <file> parameter.");

        String targetFile = FilenameUtils.concat(currentDir, args[0]);
        if (!new File(targetFile).isFile())
            throw new InvalidArgumentException("target file argument is not a valid file: " +
                    targetFile);

        String ext = FilenameUtils.getExtension(targetFile);
        if (!ext.equals("xml") && !ext.equals("k"))
            throw new InvalidArgumentException("target file format is not valid: " + ext +
                    "(should be .xml or .k)");

        String directory = getDirectoryArg(cmdOpts, Constants.DIRECTORY_OPTION, currentDir);
        String programs = getDirectoryArg(cmdOpts, Constants.PROGRAMS_OPTION,
                FilenameUtils.concat(currentDir, FilenameUtils.getFullPath(targetFile)));
        String results = getDirectoryArg(cmdOpts, Constants.RESULTS_OPTION,
                FilenameUtils.concat(currentDir, FilenameUtils.getFullPath(targetFile)));

        String[] extensions = cmdOpts.getOptionValue(Constants.EXTENSION_OPTION, "").split("\\s+");
        String[] excludes = new String[0];
        if (cmdOpts.hasOption(Constants.EXCLUDE_OPTION))
            excludes = cmdOpts.getOptionValue(Constants.EXCLUDE_OPTION).split("\\s+");

        boolean generateReport = cmdOpts.hasOption(Constants.REPORT_OPTION);

        boolean verbose = cmdOpts.hasOption(Constants.VERBOSE_OPTION);

        boolean updateOut = cmdOpts.hasOption(Constants.UPDATE_OUT_OPTION);
        boolean generateOut = cmdOpts.hasOption(Constants.GENERATE_OUT_OPTION);
        if (updateOut && generateOut) {
            throw new InvalidArgumentException("cannot have both options at once: --" +
                Constants.UPDATE_OUT_OPTION + " and --" + Constants.GENERATE_OUT_OPTION);
        }

        boolean ignoreWS = true;
        if (cmdOpts.hasOption(Constants.IGNORE_WS)
                && cmdOpts.getOptionValue(Constants.IGNORE_WS).equals("off"))
            ignoreWS = false;

        boolean ignoreBalancedParens = true;
        if (cmdOpts.hasOption(Constants.IGNORE_B_PARENS)
                && cmdOpts.getOptionValue(Constants.IGNORE_B_PARENS).equals("off"))
            ignoreBalancedParens = false;

        boolean dry = cmdOpts.hasOption(Constants.DRY);
        boolean debug = cmdOpts.hasOption(Constants.DEBUG);

        return new CmdArg(directory, programs, results, extensions, excludes, parseSkips(cmdOpts),
                parseThreads(cmdOpts), generateReport, targetFile, verbose,
                parseColorSetting(cmdOpts), parseTimeout(cmdOpts),
                updateOut, generateOut,
                ignoreWS, ignoreBalancedParens, dry, debug);
    }

    public String getDirectory() {
        return directory;
    }

    public String getPrograms() {
        return programs;
    }

    public String getResults() {
        return results;
    }

    public String getTargetFile() {
        return targetFile;
    }

    public Set<KTestStep> getSkips() {
        return skips;
    }

    public boolean isVerbose() {
        return verbose;
    }

    public ColorSetting getColorSetting() {
        return colorSetting;
    }

    public String[] getExtensions() {
        return extensions;
    }

    public String[] getExcludes() {
        return excludes;
    }

    public int getTimeout() {
        return timeout;
    }

    public boolean getUpdateOut() {
        return updateOut;
    }

    public boolean getGenerateOut() {
        return generateOut;
    }

    public boolean getGenerateReport() {
        return generateReport;
    }

    public boolean getDry() {
        return dry;
    }

    public int getThreads() {
        return threads;
    }

    public CmdArg setDirectory(String directory) {
        this.directory = directory;
        return this;
    }

    public CmdArg setPrograms(String programs) {
        this.programs = programs;
        return this;
    }

    public CmdArg setResults(String results) {
        this.results = results;
        return this;
    }

    public CmdArg setTargetFile(String targetFile) {
        this.targetFile = targetFile;
        return this;
    }

    public StringMatcher getDefaultStringMatcher() {
        return new IgnoringStringMatcher(ignoreWS, ignoreBalancedParens);
    }

    private static int parseTimeout(CommandLine cmdOpts) throws InvalidArgumentException {
        String timeout_str = cmdOpts.getOptionValue(Constants.TIMEOUT_OPTION, "300000");
        try {
            return Integer.parseInt(timeout_str);
        } catch (NumberFormatException e) {
            throw new InvalidArgumentException("timeout value is not an integer: " + timeout_str);
        }
    }

    private static Set<KTestStep> parseSkips(CommandLine cmdOpts) throws InvalidArgumentException {
        Set<KTestStep> skips = new HashSet<>();
        for (String s : cmdOpts.getOptionValue(Constants.SKIP_OPTION, "").split("\\s+"))
            switch (s.trim()) {
                case "kompile": skips.add(KTestStep.KOMPILE); break;
                case "pdf": skips.add(KTestStep.PDF); break;
                case "krun": skips.add(KTestStep.KRUN); break;
                case "": break;
                default: throw new InvalidArgumentException("--" + Constants.SKIP_OPTION + " " +
                        "option should be [kompile|pdf|krun]+");
            }
        return skips;
    }

    private static ColorSetting parseColorSetting(CommandLine cmdOpts)
            throws InvalidArgumentException {
        String s = cmdOpts.getOptionValue(Constants.COLOR_SETTING, "on");
        switch (s) {
            case "on": return ColorSetting.ON;
            case "off": return ColorSetting.OFF;
            case "extended": return ColorSetting.EXTENDED;
            default: throw new InvalidArgumentException("--" + Constants.COLOR_SETTING + " option" +
                    " should be [on|off|extended]");
        }
    }

    private static String getDirectoryArg(CommandLine cmdOpts, String argName, String default_)
            throws InvalidArgumentException {
        final String ret = cmdOpts.getOptionValue(argName, default_);
        File f = new File(ret);
        if (!f.isDirectory())
            throw new InvalidArgumentException("--" + argName + " argument is not a folder: " +
                    ret);
        return f.getAbsolutePath();
    }

    private static int parseThreads(CommandLine cmdOpts) throws InvalidArgumentException {
        String threadsStr = cmdOpts.getOptionValue("threads");
        int threads = Runtime.getRuntime().availableProcessors();
        if (threadsStr != null)
            try {
                threads = Integer.valueOf(threadsStr);
            } catch (NumberFormatException e) {
                throw new InvalidArgumentException(
                        "--threads argument should be an integer greater than 0");
            }
        if (threads <= 0)
            throw new InvalidArgumentException(
                    "--threads argument should be an integer greater than 0");
        return threads;
    }
}

