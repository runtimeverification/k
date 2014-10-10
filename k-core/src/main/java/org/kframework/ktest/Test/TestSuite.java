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

        if (!options.dry) {
            String colorCode = ColorUtil.RgbToAnsi(ret ? Color.GREEN : Color.RED,
                    options.getColorSetting(), options.getTerminalColor());
            String msg = ret ? "SUCCESS" : "FAIL (see details above)";
            System.out.format("%n%s%s%s%n", colorCode, msg, ColorUtil.ANSI_NORMAL);

            printTimeInfo();

            // save reports
            if (reportGen != null)
                reportGen.save();
        }

        return ret;
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
    private List<TestCase> runPosixOnlySteps(List<TestCase> tests)
            throws InterruptedException {
        assert OS.current().isPosix;
        int len = tests.size();
        List<TestCase> successfulTests = new ArrayList<>(len);
        List<Proc<TestCase>> ps = new ArrayList<>(len);

        System.out.format("Running initial scripts...%n");
        startTpe();
        for (TestCase tc : tests) {
            Proc<TestCase> p = tc.getPosixOnlyProc();
            if (p != null) {
                ps.add(p);
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
            if (!options.dry) {
                makeReport(p, makeRelative(tc.getDefinition()),
                        FilenameUtils.getName(tc.getPosixInitScript()));
            }
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
    private List<TestCase> runKompileSteps(List<TestCase> tests)
            throws InterruptedException {
        int len = tests.size();
        List<TestCase> successfulTests = new ArrayList<>(len);
        List<Proc<TestCase>> ps = new ArrayList<>(len);

        System.out.format("Kompile the language definitions...(%d in total)%n", len);
        long startTime = System.currentTimeMillis();
        startTpe();
        for (TestCase tc : tests) {
            Proc<TestCase> p = tc.getKompileProc();
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
            if (!options.dry) {
                makeReport(p, makeRelative(tc.getDefinition()),
                        FilenameUtils.getName(tc.getDefinition()));
            }
        }

        printResult(successfulTests.size() == len);

        return successfulTests;
    }

    /**
     * Filter test cases with same definitions for PDF step.
     * @param tests list of test cases to filter.
     * @return test cases with unique definition files.
     */
    private List<TestCase> collectPDFDefs(List<TestCase> tests) {
        Set<String> pdfDefs = new HashSet<>();
        List<TestCase> ret = new ArrayList<>();
        for (TestCase tc : tests) {
            String def = tc.getDefinition();
            if (!pdfDefs.contains(def)) {
                pdfDefs.add(def);
                ret.add(tc);
            }
        }
        return ret;
    }

    /**
     * Run pdf tests.
     * @param tests list of tests to run pdf step
     * @return whether all run successfully or not
     * @throws InterruptedException
     */
    private boolean runPDFSteps(List<TestCase> tests) throws InterruptedException {
        List<Proc<TestCase>> ps = new ArrayList<>();
        List<TestCase> pdfTests = collectPDFDefs(tests);
        int len = pdfTests.size();
        System.out.format("Generate PDF files...(%d in total)%n", len);
        startTpe();
        long startTime = System.currentTimeMillis();
        for (TestCase tc : pdfTests) {
            Proc<TestCase> p = tc.getPDFProc();
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
            if (!options.dry) {
                makeReport(p, makeRelative(tc.getDefinition()),
                        FilenameUtils.getBaseName(tc.getDefinition()) + ".pdf");
            }
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

        if (options.dry) {
            // just assume all required definitions are already compiled
            kompileSuccesses = tests;
        } else {
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
        }

        // at this point we have a subset of tests that are successfully kompiled,
        // so run programs of those tests
        int successes = 0;
        int totalTests = 0;
        for (TestCase tc : kompileSuccesses) {

            List<Proc<KRunProgram>> procs = tc.getKRunProcs();
            int inputs = 0, outputs = 0, errors = 0;
            for (Proc<KRunProgram> proc : procs) {
                KRunProgram p = proc.getObj();
                if (p.inputFile != null) inputs++;
                if (p.outputFile != null) outputs++;
                if (p.errorFile != null) errors++;
            }
            totalTests += procs.size();
            krunSteps += procs.size();

            System.out.format("Running %s programs... (%d in total, %d with input, " +
                    "%d with output, %d with error)%n", tc.getDefinition(), procs.size(),
                    inputs, outputs, errors);

            // we can have more parallelism here, but just to keep things same as old ktest,
            // I'm testing tast cases sequentially
            long startTime = System.currentTimeMillis();
            startTpe();
            for (Proc<KRunProgram> proc : procs) {
                tpe.execute(proc);
            }
            stopTpe();
            krunRealTime += System.currentTimeMillis() - startTime;

            for (Proc<KRunProgram> p : procs)
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
