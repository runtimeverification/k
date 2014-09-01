// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Test;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.ktest.*;
import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.OS;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import java.awt.*;
import java.io.*;
import java.util.*;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class TestSuite {

    private final List<TestCase> tests;
    private final KTestOptions options;
    private ThreadPoolExecutor tpe;
    private final ReportGen reportGen;

    // real times are times spend on a step, other times are total time spend by processess
    // generated for a step
    private long kompileRealTime;
    private long kompileCPUTime;
    private long pdfRealTime;
    private long pdfCPUTime;
    private long krunRealTime;
    private long krunCPUTime;
    private int kompileSteps; // total number of kompile tasks, this number is not known until
                              // ktest finishes job, because while running krun tests, adinitional
                              // compilations may be neccessary
    private int pdfSteps; // total number of pdf generation tasks
    private int krunSteps; // total number of krun tasks

    public TestSuite(List<TestCase> tests, KTestOptions options) {
        this.tests = tests;
        this.options = options;
        reportGen = options.getGenerateReport() ? new ReportGen() : null;
    }

    /**
     * Run TestSuite and return true if all tests passed.
     * @return whether all tests passed or not
     * @throws InterruptedException when some process is interrupted for some reason
     */
    public boolean run() throws InterruptedException, TransformerException,
            ParserConfigurationException, IOException {

        List<TestCase> successfulTests;

        if (OS.current().isPosix) {
            successfulTests = runPosixOnlySteps(tests);
        } else {
            successfulTests = tests;
        }

        boolean ret = successfulTests.size() == tests.size();

        Set<KTestStep> skips = options.getSkips();
        if (!skips.contains(KTestStep.KOMPILE)) {
            List<TestCase> testsIn = successfulTests;
            successfulTests = runKompileSteps(filterSkips(testsIn, KTestStep.KOMPILE));
            ret &= successfulTests.size() == testsIn.size();
        }
        if (!skips.contains(KTestStep.PDF))
            ret &= runPDFSteps(filterSkips(successfulTests, KTestStep.PDF));
        if (!skips.contains(KTestStep.KRUN))
            ret &= runKRunSteps(filterSkips(successfulTests, KTestStep.KRUN));

        String colorCode = ColorUtil.RgbToAnsi(ret ? Color.GREEN : Color.RED,
                options.getColorSetting(), options.getTerminalColor());
        String msg = ret ? "SUCCESS" : "FAIL (see details above)";
        System.out.format("%n%s%s%s%n", colorCode, msg, ColorUtil.ANSI_NORMAL);

        printTimeInfo();

        // save reports
        if (reportGen != null)
            reportGen.save();

        return ret;
    }

    /**
     * Print the commands that would be executed, but do not execute them.
     * (inspired by GNU Make)
     */
    public void dryRun() {
        Set<KTestStep> skips = options.getSkips();
        if (!skips.contains(KTestStep.KOMPILE)) {
            List<TestCase> kompileSteps = filterSkips(tests, KTestStep.KOMPILE);
            for (TestCase tc : kompileSteps)
                System.out.println(tc.toKompileLogString());
        }
        if (!skips.contains(KTestStep.PDF)) {
            List<TestCase> pdfSteps = filterSkips(tests, KTestStep.PDF);
            for (TestCase tc : pdfSteps)
                System.out.println(tc.toPdfLogString());
        }
        if (!skips.contains(KTestStep.KRUN)) {
            List<TestCase> krunSteps = filterSkips(tests, KTestStep.KRUN);
            for (TestCase tc : krunSteps) {
                List<KRunProgram> programs = tc.getPrograms();
                for (KRunProgram program : programs) {
                    StringBuilder krunLogCmd = new StringBuilder();
                    krunLogCmd.append(program.toLogString());
                    if (options.getUpdateOut() && program.outputFile != null)
                        krunLogCmd.append(" >").append(program.outputFile);
                    else if (options.getGenerateOut() && program.newOutputFile != null)
                        krunLogCmd.append(" >").append(program.newOutputFile);
                    if (program.inputFile != null)
                        krunLogCmd.append(" <").append(program.inputFile);
                    System.out.println(krunLogCmd.toString());
                }
            }
        }
    }

    private List<TestCase> filterSkips(List<TestCase> tests, KTestStep step) {
        List<TestCase> ret = new LinkedList<>();
        for (TestCase test : tests)
            if (!test.skip(step))
                ret.add(test);
        return ret;
    }

    /**
     * Run posixOnly scripts in list of test cases.
     *
     * @return list of test cases that run successfully
     * @throws InterruptedException
     */
    private List<TestCase> runPosixOnlySteps(List<TestCase> tests) throws InterruptedException {
        assert OS.current().isPosix;
        int len = tests.size();
        List<TestCase> successfulTests = new ArrayList<>(len);
        List<Proc<TestCase>> ps = new ArrayList<>(len);

        System.out.format("Running initial scripts...%n");
        startTpe();
        for (TestCase tc : tests) {
            if (tc.hasPosixOnly()) {
                Proc<TestCase> p =
                        new Proc<>(tc, tc.getPosixOnlyCmd(), tc.toPosixOnlyLogString(), options);
                ps.add(p);
                p.setWorkingDir(tc.getWorkingDir());
                tpe.execute(p);
            } else {
                successfulTests.add(tc);
            }
        }
        stopTpe();

        // collect successful test cases, report failures
        for (Proc<TestCase> p : ps) {
            TestCase tc = p.getObj();
            if (p.isSuccess())
                successfulTests.add(tc);
            makeReport(p, makeRelative(tc.getDefinition()),
                    FilenameUtils.getName(tc.getPosixInitScript()));
        }

        printResult(successfulTests.size() == len);

        return successfulTests;
    }

    /**
     * Run kompile steps in list of test cases.
     *
     * This method returns something different from others, this is because in kompile tests we
     * need to know exactly what tests passed, because otherwise we can't know what krun and
     * pdf tests to run (running krun/pdf on a broken definition doesn't make sense)
     * @return list of test cases that run successfully
     * @throws InterruptedException
     */
    private List<TestCase> runKompileSteps(List<TestCase> tests) throws InterruptedException {
        int len = tests.size();
        List<TestCase> successfulTests = new ArrayList<>(len);
        List<Proc<TestCase>> ps = new ArrayList<>(len);

        System.out.format("Kompile the language definitions...(%d in total)%n", len);
        long startTime = System.currentTimeMillis();
        startTpe();
        for (TestCase tc : tests) {
            Proc<TestCase> p = new Proc<>(tc, tc.getKompileCmd(), tc.toKompileLogString(), options);
            p.setWorkingDir(tc.getWorkingDir());
            ps.add(p);
            tpe.execute(p);
            kompileSteps++;
        }
        stopTpe();
        kompileRealTime += System.currentTimeMillis() - startTime;

        // collect successful test cases, report failures
        for (Proc<TestCase> p : ps) {
            kompileCPUTime += p.getTimeDelta();
            TestCase tc = p.getObj();
            if (p.isSuccess())
                successfulTests.add(tc);
            makeReport(p, makeRelative(tc.getDefinition()),
                    FilenameUtils.getName(tc.getDefinition()));
        }

        printResult(successfulTests.size() == len);

        return successfulTests;
    }

    /**
     * Run pdf tests.
     * @param tests list of tests to run pdf step
     * @return whether all run successfully or not
     * @throws InterruptedException
     */
    private boolean runPDFSteps(List<TestCase> tests) throws InterruptedException {
        List<Proc<TestCase>> ps = new ArrayList<>();
        int len = tests.size();
        System.out.format("Generate PDF files...(%d in total)%n", len);
        startTpe();
        long startTime = System.currentTimeMillis();
        for (TestCase tc : tests) {
            Proc<TestCase> p = new Proc<>(tc, tc.getPdfCmd(), tc.toPdfLogString(), options);
            p.setWorkingDir(tc.getWorkingDir());
            ps.add(p);
            tpe.execute(p);
            pdfSteps++;
        }
        stopTpe();
        pdfRealTime += System.currentTimeMillis() - startTime;

        boolean ret = true;
        for (Proc<TestCase> p : ps) {
            pdfCPUTime += p.getTimeDelta();
            TestCase tc = p.getObj();
            if (!p.isSuccess())
                ret = false;
            makeReport(p, makeRelative(tc.getDefinition()),
                    FilenameUtils.getBaseName(tc.getDefinition()) + ".pdf");
        }

        printResult(ret);

        return ret;
    }

    /**
     * Run krun tests.
     * @param tests list of test cases to run krun steps
     * @return whether all run successfully or not
     * @throws InterruptedException
     */
    private boolean runKRunSteps(List<TestCase> tests) throws InterruptedException {
        List<TestCase> kompileSuccesses = new LinkedList<>();

        // collect definitions that are not yet kompiled and kompile them first
        ArrayList<TestCase> notKompiled = new ArrayList<>();
        for (TestCase tc : tests) {
            if (!tc.isDefinitionKompiled())
                notKompiled.add(tc);
            else
                kompileSuccesses.add(tc);
        }

        if (!notKompiled.isEmpty()) {
            System.out.println("Kompiling definitions that are not yet kompiled.");
            kompileSuccesses.addAll(runKompileSteps(notKompiled));
        }

        // at this point we have a subset of tests that are successfully kompiled,
        // so run programs of those tests
        int successes = 0;
        int totalTests = 0;
        for (TestCase tc : kompileSuccesses) {

            List<KRunProgram> programs = tc.getPrograms();
            int inputs = 0, outputs = 0, errors = 0;
            for (KRunProgram p : programs) {
                if (p.inputFile != null) inputs++;
                if (p.outputFile != null) outputs++;
                if (p.errorFile != null) errors++;
            }

            System.out.format("Running %s programs... (%d in total, %d with input, " +
                    "%d with output, %d with error)%n", tc.getDefinition(), programs.size(),
                    inputs, outputs, errors);

            // we can have more parallelism here, but just to keep things same as old ktest,
            // I'm testing tast cases sequentially
            List<Proc<KRunProgram>> testCaseProcs = new ArrayList<>(programs.size());
            long startTime = System.currentTimeMillis();
            startTpe();
            for (KRunProgram program : programs) {
                testCaseProcs.add(runKRun(program));
                totalTests++;
            }
            stopTpe();
            krunRealTime += System.currentTimeMillis() - startTime;

            for (Proc<KRunProgram> p : testCaseProcs)
                if (p != null) // p may be null when krun test is skipped because of missing
                               // input file
                {
                    krunCPUTime += p.getTimeDelta();
                    KRunProgram pgm = p.getObj();
                    makeReport(p, makeRelative(tc.getDefinition()),
                            FilenameUtils.getName(pgm.pgmName));
                    if (p.isSuccess())
                        successes++;
                }
        }
        printResult(successes == totalTests);
        return successes == totalTests;
    }

    private void startTpe() {
        int nThreads;
        if (options.getUpdateOut() || options.getGenerateOut()) {
            nThreads = 1;
        } else {
            nThreads = options.getThreads();
        }
        tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(nThreads);
    }

    private void stopTpe() throws InterruptedException {
        tpe.shutdown();
        while (!tpe.awaitTermination(1, TimeUnit.SECONDS));
    }

    /**
     * Execute a krun step.
     * @param program KRunProgram object that holds required information to run a krun process
     * @return Proc object for krun process
     */
    private Proc<KRunProgram> runKRun(KRunProgram program) {
        String[] args = program.getKrunCmd();

        // passing null to Proc is OK, it means `ignore'
        String inputContents = null, outputContents = null, errorContents = null;
        if (program.inputFile != null)
            try {
                inputContents = IOUtils.toString(new FileInputStream(new File(program.inputFile)));
            } catch (IOException e) {
                System.out.format("WARNING: cannot read input file %s -- skipping program %s%n",
                        program.inputFile, program.args.get(1));
                // this case happens when an input file is found by TestCase,
                // but somehow file is not readable. in that case there's no point in running the
                // program because it'll wait for input forever.
                return null;
            }
        if (program.outputFile != null)
            try {
                outputContents = IOUtils.toString(new FileInputStream(
                        new File(program.outputFile)));
            } catch (IOException e) {
                System.out.format("WARNING: cannot read output file %s -- program output " +
                        "won't be matched against output file%n", program.outputFile);
            }
        if (program.errorFile != null)
            try {
                errorContents = IOUtils.toString(new FileInputStream(
                        new File(program.errorFile)));
            } catch (IOException e) {
                System.out.format("WARNING: cannot read error file %s -- program error output "
                        + "won't be matched against error file%n", program.errorFile);
            }

        // Annotate expected output and error messages with paths of files that these strings
        // are defined in (to be used in error messages)
        Annotated<String, String> outputContentsAnn = null;
        if (outputContents != null)
            outputContentsAnn = new Annotated<>(outputContents, program.outputFile);

        Annotated<String, String> errorContentsAnn = null;
        if (errorContents != null)
            errorContentsAnn = new Annotated<>(errorContents, program.errorFile);

        StringMatcher matcher = options.getDefaultStringMatcher();
        if (program.regex) {
            matcher = new RegexStringMatcher();
        }
        Proc<KRunProgram> p = new Proc<>(program, args, program.inputFile, inputContents,
                outputContentsAnn, errorContentsAnn, program.toLogString(), matcher, options,
                program.outputFile, program.newOutputFile);
        p.setWorkingDir(new File(program.defPath));
        tpe.execute(p);
        krunSteps++;
        return p;
    }

    private void printResult(boolean condition) {
        if (condition)
            System.out.println("SUCCESS");
        else {
            System.out.println(ColorUtil.RgbToAnsi(
                    Color.RED, options.getColorSetting(), options.getTerminalColor())
                    + "FAIL"
                    + ColorUtil.ANSI_NORMAL);
        }
    }

    private String makeRelative(String absolutePath) {
        // I'm not sure if this works as expected, but I'm simply removing prefix of absolutePath
        String pathRegex = System.getProperty("user.dir")
                // on Windows, `\` characters in file paths are causing problem, so we need to
                // escape one more level:
                .replaceAll("\\\\", "\\\\\\\\");
        return absolutePath.replaceFirst(pathRegex, "");
    }

    private void makeReport(Proc<?> p, String definition, String testName) {
        if (reportGen == null)
            return;
        if (p.isSuccess())
            reportGen.addSuccess(definition, testName,
                    p.getTimeDelta(), p.getPgmOut(), p.getPgmErr());
        else
            reportGen.addFailure(definition, testName,
                    p.getTimeDelta(), p.getPgmOut(), p.getPgmErr(), p.getReason());
    }

    private void printTimeInfo() {
        long kompileCPUTime = this.kompileCPUTime / 1000;
        long pdfCPUTime = this.pdfCPUTime / 1000;
        long krunCPUTime = this.krunCPUTime / 1000;

        long kompileRealTime = this.kompileRealTime / 1000;
        long pdfRealTime = this.pdfRealTime / 1000;
        long krunRealTime = this.krunRealTime / 1000;

        String defInfo = String.format(
                "Definitions kompiled: %s (time: %s'%s'' elapsed, %s'%s'' CPU)%n",
                kompileSteps,
                kompileRealTime / 60, kompileRealTime % 60,
                kompileCPUTime / 60, kompileCPUTime % 60);
        String pdfInfo = String.format(
                "PDF posters kompiled: %s (time: %s'%s'' elapsed, %s'%s'' CPU)%n",
                pdfSteps,
                pdfRealTime / 60, pdfRealTime % 60,
                pdfCPUTime / 60, pdfCPUTime % 60);
        String krunInfo = String.format(
                "Programs krun: %s (time: %s'%s'' elapsed, %s'%s'' CPU)%n",
                krunSteps,
                krunRealTime / 60, krunRealTime % 60,
                krunCPUTime / 60, krunCPUTime % 60);

        long totalRealTime = kompileRealTime + pdfRealTime + krunRealTime;
        long totalCPUTime = kompileCPUTime + pdfCPUTime + krunCPUTime;
        String totalInfo = String.format(
                "Total time: %s'%s'' elapsed, %s'%s'' CPU%n",
                totalRealTime / 60, totalRealTime % 60,
                totalCPUTime / 60, totalCPUTime % 60);

        StringBuilder sb = new StringBuilder();
        sb.append("----------------------------\n");
        sb.append(defInfo).append(pdfInfo).append(krunInfo).append(totalInfo);
        sb.append("----------------------------\n");

        System.out.println(sb);
    }
}
