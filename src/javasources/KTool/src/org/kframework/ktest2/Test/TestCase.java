package org.kframework.ktest2.Test;


import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest2.Annotated;
import org.kframework.ktest2.CmdArgs.CmdArg;
import org.kframework.ktest2.Config.InvalidConfigError;
import org.kframework.ktest2.Config.LocationData;
import org.kframework.ktest2.KTestStep;
import org.kframework.ktest2.PgmArg;

import java.io.File;
import java.util.*;

public class TestCase {

    /**
     * Absolute path of K definition file.
     */
    private final Annotated<String, LocationData> definition;

    /**
     * Absolute paths of program files directories.
     */
    private final Set<Annotated<String, LocationData>> programs;

    /**
     * Valid extensions for programs. (without dot)
     */
    private final Set<String> extensions;

    /**
     * Program names that are excluded from krun processes.
     */
    private Set<String> excludes;

    /**
     * Absolute path of result files directories.
     */
    private final Set<Annotated<String, LocationData>> results;

    /**
     * List of command line arguments to pass to kompile.
     */
    private List<PgmArg> kompileOpts;

    /**
     * List of command line arguments to pass to krun.
     */
    private List<PgmArg> krunOpts;

    /**
     * Program full path, list of kompile arguments pairs.
     */
    private Map<String, List<PgmArg>> pgmSpecificKRunOpts;

    /**
     * Which tests to skip for this particular test case.
     */
    private final Set<KTestStep> skips;

    public TestCase(Annotated<String, LocationData> definition,
                    List<Annotated<String, LocationData>> programs,
                    String[] extensions,
                    String[] excludes,
                    List<Annotated<String, LocationData>> results,
                    List<PgmArg> kompileOpts,
                    List<PgmArg> krunOpts,
                    Map<String, List<PgmArg>> pgmSpecificKRunOpts,
                    Set<KTestStep> skips) throws InvalidConfigError {
        this.definition = definition;
        this.programs = toSet(programs);
        this.extensions = toSet(extensions);
        this.excludes = toSet(excludes);
        this.results = toSet(results);
        this.kompileOpts = kompileOpts;
        this.krunOpts = krunOpts;
        this.pgmSpecificKRunOpts = pgmSpecificKRunOpts;
        this.skips = skips;
        this.validateTestCase();
    }

    public static TestCase makeTestCaseFromK(CmdArg cmdArgs) throws InvalidConfigError {
        Annotated<String, LocationData> targetFile =
                new Annotated<>(cmdArgs.targetFile, new LocationData());

        List<Annotated<String, LocationData>> programs = new LinkedList<>();
        programs.add(new Annotated<>(cmdArgs.results, new LocationData()));

        List<Annotated<String,LocationData>> results = new LinkedList<>();
        results.add(new Annotated<>(cmdArgs.results, new LocationData()));

        List<PgmArg> emptyOpts = new ArrayList<>(0);

        HashMap<String, List<PgmArg>> emptyOptsMap = new HashMap<>(0);

        return new TestCase(targetFile, programs, cmdArgs.extensions,
                cmdArgs.excludes, results, emptyOpts, emptyOpts, emptyOptsMap,
                new HashSet<KTestStep>());
    }

    public boolean isDefinitionKompiled() {
        return new File(FilenameUtils.concat(FilenameUtils.getFullPath(definition.getObj()),
                FilenameUtils.getBaseName(definition.getObj()) + "-kompiled")).isDirectory();
    }

    /**
     * Generate set of programs to run for this test case.
     * @return set of programs to krun
     */
    public List<KRunProgram> getPrograms() {
        List<KRunProgram> ret = new LinkedList<>();
        for (Annotated<String, LocationData> pgmDir : programs)
            ret.addAll(searchPrograms(pgmDir.getObj()));
        return ret;
    }

    /**
     * @return absolute path of definition file
     */
    public String getDefinition() {
        assert new File(definition.getObj()).isFile();
        return definition.getObj();
    }

    /**
     * @return program options to pass kompile process
     */
    public List<PgmArg> getKompileOpts() {
        return kompileOpts;
    }

    public void setKompileOpts(List<PgmArg> kompileOpts) {
        this.kompileOpts = kompileOpts;
    }

    public void setExcludes(String[] excludes) {
        this.excludes = toSet(excludes);
    }

    public void setKrunOpts(List<PgmArg> krunOpts) {
        this.krunOpts = krunOpts;
    }

    public void setPgmSpecificKRunOpts(Map<String, List<PgmArg>> pgmSpecificKRunOpts) {
        this.pgmSpecificKRunOpts = pgmSpecificKRunOpts;
    }

    /**
     * Do we need to skip a step for this test case?
     * @param step step to skip
     * @return whether to skip the step or not
     */
    public boolean skip(KTestStep step) {
        return skips.contains(step);
    }

    private void validateTestCase() throws InvalidConfigError {
        if (!new File(definition.getObj()).isFile())
            throw new InvalidConfigError(
                    "definition file " + definition.getObj() + " is not a file.",
                    definition.getAnn());
        for (Annotated<String, LocationData> p : programs)
            if (!new File(p.getObj()).isDirectory())
                throw new InvalidConfigError(
                        "program directory " + p.getObj() + " is not a directory.",
                        p.getAnn());
        for (Annotated<String, LocationData> r : results)
            if (!new File(r.getObj()).isDirectory())
                throw new InvalidConfigError(
                        "result directory " + r.getObj() + " is not a directory.",
                        r.getAnn());
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

                    String definitionFilePath =
                            FilenameUtils.getFullPathNoEndSeparator(definition.getObj());
                    String inputFilePath = searchFile(inputFileName, results);
                    String outputFilePath = searchFile(outputFileName, results);
                    String errorFilePath = searchFile(errorFileName, results);

                    // set krun args
                    List<String> args = new LinkedList<>();
                    args.add(pgmFilePath);
                    for (PgmArg arg : getPgmOptions(pgmFilePath))
                        args.add(arg.toString());
                    args.add(new PgmArg("directory", definitionFilePath).toString());

                    ret.add(new KRunProgram(FilenameUtils.getBaseName(pgmFilePath),
                            args, inputFilePath, outputFilePath, errorFilePath));
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
    private String searchFile(String fname, Set<Annotated<String, LocationData>> dirs) {
        for (Annotated<String, LocationData> dir : dirs) {
            // TODO: validate validate validate validate validate
            // (forgetting to pass --programs or makes this part break) (osa1)
            String ret = searchFile(fname, dir.getObj());
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

    private <T> Set<T> toSet(T[] arr) {
        Set<T> ret = new HashSet<>();
        Collections.addAll(ret, arr);
        return ret;
    }

    private <T> Set<T> toSet(List<T> lst) {
        Set<T> ret = new HashSet<>();
        for (T e : lst)
            ret.add(e);
        return ret;
    }
}
