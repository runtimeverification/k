// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.CmdArgs;

import org.apache.commons.io.FilenameUtils;
import org.kframework.krun.ColorOptions;
import org.kframework.krun.ColorSetting;
import org.kframework.ktest.IgnoringStringMatcher;
import org.kframework.ktest.KTestStep;
import org.kframework.ktest.StringMatcher;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.EnumSetConverter;
import org.kframework.utils.options.OnOffConverter;
import org.kframework.utils.options.PositiveInteger;
import org.kframework.utils.options.StringListConverter;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;

import java.awt.Color;
import java.io.File;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

/**
 * Represents valid command line arguments. This class must call the
 * `validateArgs' method, which ensures validation of arguments, before use.
 *
 * Being valid means:
 *   - File paths are valid(e.g. point to a files/directories) relative to current directory
 *   - Only one unnamed argument is passed
 *   - File extension is either .k or .xml
 */
public class KTestOptions {

    public KTestOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public KTestOptions(Void v) {}

    public static final class KTestStepSetConverter extends EnumSetConverter<KTestStep, KTestStepConverter> {

        public KTestStepSetConverter(String optionName) {
            super(optionName);
        }

        @Override
        public KTestStepConverter enumConverter() {
            return new KTestStepConverter(getOptionName());
        }
    }

    public static final class KTestStepConverter extends BaseEnumConverter<KTestStep> {

        public KTestStepConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<KTestStep> enumClass() {
            return KTestStep.class;
        }
    }

    @ParametersDelegate
    private transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    private ColorOptions color = new ColorOptions();

    /**
     * A root directory where K definitions reside. By default this is the current directory.
     * Valid only in batch mode.
     */
    @Parameter(names={"-d", "--directory"}, description="A root directory where K definitions reside." +
                        " By default this is the current directory. Valid only in batch mode.")
    private String _directory;

    /**
     * Programs directory in single job mode, or a root directory for programs in batch mode. By
     * default this is the directory where <file> reside.
     */
    @Parameter(names="--programs", description="Programs directory in single job mode, " +
                        "or a root directory for programs in batch mode. By default this is the " +
                        "directory where <file> reside.")
    private String _programs;

    /**
     * Directory containing input and expected output for programs in single job mode,
     * or a root directory for the expected I/O for programs in batch mode. By default this is
     * the directory where <file> reside.
     */
    @Parameter(names="--results", description="Directory containing input and expected " +
                        "output for programs in single job mode, or a root directory for the " +
                        "expected I/O for programs in batch mode. By default this is the " +
                        "directory where <file> reside.")
    private String _results;

    // contains the values processed from external state
    private String directory, programs, results, targetFile;

    /**
     * The list of program extensions separated by whitespaces. Required in single job mode,
     * invalid in batch mode.
     */
    @Parameter(names="--extension", description="The list of program extensions separated " +
                        "by whitespaces. Required in single job mode, invalid in batch mode.",
                        listConverter=StringListConverter.class)
    private List<String> extensions = new ArrayList<>();

    /**
     * The list of programs which will not be tested. Valid only in single job mode.
     */
    @Parameter(names="--exclude", description="The list of programs which will not be " +
                        "tested. Valid only in single job mode.",
                        listConverter=StringListConverter.class)
    private List<String> excludes = new ArrayList<>();

    /**
     * The list of steps separated by whitespace to be skipped.
     */
    @Parameter(names="--skip", description="The list of steps to be skipped, separated by whitespace. " +
                        "A step is either [" + "kompile" + "|" + "pdf" +
                        "|" + "krun" + "].",
                        converter=KTestStepSetConverter.class)
    private Set<KTestStep> skips = EnumSet.noneOf(KTestStep.class);

    /**
     * Maximum number of threads spawned for parallel execution.
     */
    @Parameter(names="--threads", description="Maximum number of threads spawned for parallel execution.",
            validateValueWith=PositiveInteger.class)
    private int threads = Runtime.getRuntime().availableProcessors();

    /**
     * Generate a junit-like report.
     */
    @Parameter(names="--report", description="Generate a junit-like report.")
    private boolean generateReport = false;

    /**
     * Config XML file for batch mode, K definition for single job mode.
     */
    @Parameter(description="<file>")
    private List<String> parameters;

    /**
     * Timeout for processes spawned by ktest. (in seconds)
     */
    @Parameter(names="--timeout", description="Time limit for each process (milliseconds).")
    private int timeout = 300000;

    /**
     * Update existing .out files.
     */
    @Parameter(names="--update-out", description="Update existing .out files.")
    private boolean updateOut = false;

    /**
     * Newly generate .out files if needed.
     */
    @Parameter(names="--generate-out", description="Newly generate .out files if needed.")
    private boolean generateOut = false;

    /**
     * Ignore whitespace while comparing program outputs.
     */
    @Parameter(names="--ignore-whitespace", description="Ignore white spaces when comparing results.",
            arity=1, converter=OnOffConverter.class)
    private boolean ignoreWS = true;

    /**
     * Ignore balanced parens while comparing program outputs.
     */
    @Parameter(names="--ignore-balanced-parens", description="Ignore balanced parentheses when " +
                        "comparing results.", arity=1, converter=OnOffConverter.class)
    private boolean ignoreBalancedParens = true;

    /**
     * Dry run.
     */
    @Parameter(names="--dry", description="Dry run: print out the " +
                "command to be executed without actual execution.")
    public boolean dry = false;

    /**
     * Enable debugging. When enabled, KTest passes --debug to spawned processes.
     */
    private boolean debug = false;

    public final long start = System.currentTimeMillis();

    /**
     * Copy constructor.
     * @param obj KTestOptions object to copy
     */
    public KTestOptions(KTestOptions obj) {
        this.directory = obj.directory;
        this.programs = obj.programs;
        this.results = obj.results;
        this.extensions = obj.extensions;
        this.excludes = obj.excludes;
        this.skips = obj.skips;
        this.threads = obj.threads;
        this.generateReport = obj.generateReport;
        this.parameters = obj.parameters;
        this.global = obj.global;
        this.color = obj.color;
        this.timeout = obj.timeout;
        this.updateOut = obj.updateOut;
        this.generateOut = obj.generateOut;
        this.ignoreWS = obj.ignoreWS;
        this.ignoreBalancedParens = obj.ignoreBalancedParens;
        this.dry = obj.dry;
        this.debug = obj.debug;
    }

    /**
     * Validate raw data parsed from command line arguments and set fields,
     * which are needed for TestSuite to run tests.
     * @throws ParameterException in case of an invalid argument
     */
    public void validateArgs(FileUtil files) throws ParameterException {
        String currentDir = files.resolveWorkingDirectory(".").getAbsolutePath();

        if (parameters == null || parameters.size() != 1)
            throw new ParameterException("ktest requires exactly one <file> parameter.");

        targetFile = FilenameUtils.concat(currentDir, parameters.get(0));
        if (!new File(targetFile).isFile())
            throw new ParameterException("target file argument is not a valid file: " +
                    targetFile);

        String ext = FilenameUtils.getExtension(targetFile);
        if (!ext.equals("xml") && !ext.equals("k"))
            throw new ParameterException("target file format is not valid: " + ext +
                    "(should be .xml or .k)");

        directory = getDirectoryArg("directory", _directory, currentDir, files);
        programs = getDirectoryArg("programs", _programs,
                FilenameUtils.concat(currentDir, FilenameUtils.getFullPath(targetFile)), files);
        results = getDirectoryArg("results", _results,
                FilenameUtils.concat(currentDir, FilenameUtils.getFullPath(targetFile)), files);

        if (updateOut && generateOut) {
            throw new ParameterException("cannot have both options at once: --" +
                    "update-out" + " and --" + "generate-out");
        }
    }

    public GlobalOptions getGlobal() {
        return global;
    }

    public String getDirectory() {
        return directory;
    }

    public String getPrograms() {
        return programs;
    }

    public boolean programsSpecified() {
        return _programs != null;
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
        return global.verbose;
    }

    public ColorSetting getColorSetting() {
        return color.color();
    }

    public Color getTerminalColor() {
        return color.terminalColor();
    }

    public ColorOptions getColorOptions() {
        return color;
    }

    public List<String> getExtensions() {
        return extensions;
    }

    public List<String> getExcludes() {
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

    public boolean getDebug() {
        return debug;
    }

    public int getThreads() {
        return threads;
    }

    public void setDebug(boolean debug) {
        this.debug = debug;
    }

    public KTestOptions setDirectory(String directory) {
        this.directory = directory;
        return this;
    }

    public KTestOptions setPrograms(String programs) {
        this.programs = programs;
        return this;
    }

    public KTestOptions setResults(String results) {
        this.results = results;
        return this;
    }

    public KTestOptions setTargetFile(String targetFile) {
        this.targetFile = targetFile;
        return this;
    }

    public StringMatcher getDefaultStringMatcher() {
        return new IgnoringStringMatcher(ignoreWS, ignoreBalancedParens);
    }

    private static String getDirectoryArg(String argName, String value, String default_, FileUtil files)
            throws ParameterException {
        final String ret = (value == null ? default_ : value);
        File f = files.resolveWorkingDirectory(ret);
        if (!f.isDirectory())
            throw new ParameterException("--" + argName + " argument is not a folder: " +
                    ret);
        return f.getAbsolutePath();
    }
}

