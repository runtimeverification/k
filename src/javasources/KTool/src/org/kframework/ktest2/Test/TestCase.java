package org.kframework.ktest2.Test;


import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest2.CmdArgs.CmdArg;
import org.kframework.ktest2.Config.InvalidConfigError;
import org.kframework.ktest2.PgmArg;

import java.io.File;
import java.util.*;

public class TestCase {

    /**
     * Absolute path of K definition file.
     */
    private final String definition;

    /**
     * Absolute paths of program files directories.
     */
    private final Set<String> programs;

    /**
     * Valid extensions for programs. (without dot)
     */
    private final Set<String> extensions;

    /**
     * Program names that are excluded from krun processes.
     */
    private final Set<String> excludes;

    /**
     * Absolute path of result files directories.
     */
    private final Set<String> results;

    /**
     * List of command line arguments to pass to kompile.
     */
    private final List<PgmArg> kompileOpts;

    /**
     * List of command line arguments to pass to krun.
     */
    private final List<PgmArg> krunOpts;

    /**
     * Program full path, list of kompile arguments pairs.
     */
    private final Map<String, List<PgmArg>> pgmSpecificKRunOpts;


    // TODO: add something like validateArgs to make sure only valid test cases are produced (osa1)
    public TestCase(String definition, String[] programs, String[] extensions,
                    String[] excludes, String[] results, List<PgmArg> kompileOpts,
                    List<PgmArg> krunOpts, Map<String, List<PgmArg>> pgmSpecificKRunOpts)
            throws InvalidConfigError {
        this.definition = definition;
        this.programs = toSet(programs);
        this.extensions = toSet(extensions);
        this.excludes = toSet(excludes);
        this.results = toSet(results);
        this.kompileOpts = kompileOpts;
        this.krunOpts = krunOpts;
        this.pgmSpecificKRunOpts = pgmSpecificKRunOpts;
        this.validateTestCase();
    }

    public static TestCase makeTestCaseFromK(CmdArg cmdArgs) throws InvalidConfigError {
        String[] programs = new String[]{cmdArgs.programs};
        String[] results = new String[]{cmdArgs.results};
        List<PgmArg> emptyOpts = new ArrayList<>(0);
        HashMap<String, List<PgmArg>> emptyOptsMap = new HashMap<>(0);
        return new TestCase(cmdArgs.targetFile, programs, cmdArgs.extensions,
                cmdArgs.excludes, results, emptyOpts, emptyOpts, emptyOptsMap);
    }

    /**
     * @return absolute path of definition file
     */
    public String getDefinition() {
        assert new File(definition).isFile();
        return definition;
    }

    /**
     * @return program options to pass kompile process
     */
    public List<PgmArg> getKompileOpts() {
        return kompileOpts;
    }

    public boolean isDefinitionKompiled() {
        return new File(FilenameUtils.concat(FilenameUtils.getFullPath(definition),
                FilenameUtils.getBaseName(definition) + "-kompiled")).isDirectory();
    }

    /**
     * Generate set of programs to run for this test case.
     * @return set of programs to krun
     */
    public List<KRunProgram> getPrograms() {
        List<KRunProgram> ret = new LinkedList<>();
        for (String pgmDir : programs)
            ret.addAll(searchPrograms(pgmDir));
        return ret;
    }

    private void validateTestCase() throws InvalidConfigError {
        if (!new File(definition).isFile())
            throw new InvalidConfigError("definition file " + definition + " is not a file.");
        for (String s : programs)
            if (!new File(s).isDirectory())
                throw new InvalidConfigError("program directory " + s + " is not a directory.");
        for (String s : results)
            if (!new File(s).isDirectory())
                throw new InvalidConfigError("result directory " + s + " is not a directory.");
    }

    private List<PgmArg> getPgmOptions(String pgm) {
        List<PgmArg> ret = pgmSpecificKRunOpts.get(pgm);
        // TODO: I'm using all-programs options only when no program specific options specified,
        // make sure this is intended behavior (osa1)
        if (ret == null)
            return krunOpts;
        return ret;
    }

    /**
     * Search for program files by taking program extensions and excluded files into account.
     * @param pgmDir Root folder to start searching
     * @return list of KRunPrograms
     */
    private List<KRunProgram> searchPrograms(String pgmDir) {
        List<KRunProgram> ret = new LinkedList<>();
        for (File pgmFile : new File(pgmDir).listFiles()) {
            if (pgmFile.isFile()) {
                String pgmFilePath = pgmFile.getAbsolutePath();
                if (extensions.contains(FilenameUtils.getExtension(pgmFilePath))) {
                    // skip excluded files
                    boolean exclude = false;
                    for (String excludedPattern : excludes)
                            if (pgmFilePath.contains(excludedPattern))
                                exclude = true;
                    if (exclude)
                        continue;

                    // find result files
                    String inputFileName = FilenameUtils.getName(pgmFilePath) + ".in";
                    String outputFileName = FilenameUtils.getName(pgmFilePath) + ".out";
                    String errorFileName = FilenameUtils.getName(pgmFilePath) + ".err";

                    String definitionFilePath = FilenameUtils.getFullPathNoEndSeparator(definition);
                    String inputFilePath = searchFile(inputFileName, results);
                    String outputFilePath = searchFile(outputFileName, results);
                    String errorFilePath = searchFile(errorFileName, results);

                    // set krun args
                    List<String> args = new LinkedList<>();
                    args.add(pgmFilePath);
                    for (PgmArg arg : getPgmOptions(pgmFilePath))
                        args.add(arg.toString());
                    args.add(new PgmArg("directory", definitionFilePath).toString());

                    ret.add(new KRunProgram(args, inputFilePath, outputFilePath, errorFilePath));
                }
            } else {
                ret.addAll(searchPrograms(pgmFile.getAbsolutePath()));
            }
        }
        return ret;
    }

    /**
     * Search file in set of directories.
     * Search is recursive, meaning that subfolders are also searched.
     * @param fname file name (not path)
     * @param dirs set of directories to search
     * @return absolute path if file is found, null otherwise
     */
    private String searchFile(String fname, Set<String> dirs) {
        for (String dir : dirs) {
            // TODO: validate validate validate validate validate
            // (forgetting to pass --programs or makes this part break) (osa1)
            String ret = searchFile(fname, dir);
            if (ret != null)
                return ret;
        }
        return null;
    }

    /**
     * Search file recursively in dir.
     * @param fname file name
     * @param dir root directory to start searching
     * @return absolute path if found, null if not
     */
    private String searchFile(String fname, String dir) {
        for (File f : new File(dir).listFiles()) {
            if (f.isFile() && f.getName().equals(fname))
                return f.getAbsolutePath();
            else if (f.isDirectory()) {
                String ret = searchFile(fname, f.getAbsolutePath());
                if (ret != null)
                    return ret;
            }
        }
        return null;
    }

    private Set<String> toSet(String[] arr) {
        Set<String> ret = new HashSet<>();
        Collections.addAll(ret, arr);
        return ret;
    }
}
