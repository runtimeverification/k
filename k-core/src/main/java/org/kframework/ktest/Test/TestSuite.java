// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Test;

import com.google.common.collect.Iterables;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.*;
import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.file.FileUtil;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;

import java.awt.*;
import java.io.*;
import java.util.List;

public class TestSuite {

    private final List<TestCase> tests;
    private final KTestOptions options;
    private final ReportGen reportGen;

    public TestSuite(List<TestCase> tests, KTestOptions options, FileUtil files) {
        this.tests = tests;
        this.options = options;
        reportGen = options.getGenerateReport() ? new ReportGen(files.resolveWorkingDirectory("junit-reports")) : null;
    }

    public boolean run() throws IOException, TransformerException, ParserConfigurationException {
        TaskQueue queue = new TaskQueue(options);
        for (TestCase test : tests) {
            queue.addTask(test);
        }
        queue.terminate();

        if (options.dry) {
            return true;
        }

        List<Proc<TestCase>> scriptProcs = queue.getScriptProcs();
        List<Proc<TestCase>> kompileProcs = queue.getKompileProcs();
        List<Proc<TestCase>> pdfProcs = queue.getPdfProcs();
        List<Proc<KRunProgram>> krunProcs = queue.getKrunProcs();

        boolean success = true;
        long cpuTimeSpent = 0;
        long realTimeSpent = queue.getLastTestFinished() - options.start;
        Iterable<Proc> allProcs = Iterables.concat(scriptProcs, kompileProcs, pdfProcs, krunProcs);
        for (Proc p : allProcs) {
            success &= p.isSuccess();
            cpuTimeSpent += p.getTimeDelta();
        }

        String colorCode = ColorUtil.RgbToAnsi(success ? Color.GREEN : Color.RED,
                options.getColorSetting(), options.getTerminalColor());
        String msg = success ? "SUCCESS" : "FAIL (see details above)";
        System.out.format("%n%s%s%s%n", colorCode, msg, ColorUtil.ANSI_NORMAL);

        printTimeInfo(cpuTimeSpent / 1000, realTimeSpent / 1000,
                kompileProcs.size(), pdfProcs.size(), krunProcs.size());

        // generate reports
        for (Proc<TestCase> p : scriptProcs) {
            TestCase tc = p.getObj();
            makeReport(p, tc.getDefinition(),
                    FilenameUtils.getName(tc.getPosixInitScript()));
        }
        for (Proc<TestCase> p : kompileProcs) {
            TestCase tc = p.getObj();
            makeReport(p, tc.getDefinition(),
                    FilenameUtils.getName(tc.getDefinition()));
        }
        for (Proc<TestCase> p : pdfProcs) {
            TestCase tc = p.getObj();
            makeReport(p, tc.getDefinition(),
                    FilenameUtils.getBaseName(tc.getDefinition()) + ".pdf");
        }
        for (Proc<KRunProgram> p : krunProcs) {
            KRunProgram pgm = p.getObj();
            makeReport(p, pgm.defPath.getAbsolutePath(), FilenameUtils.getName(pgm.pgmName));
        }

        if (reportGen != null) {
            reportGen.save();
        }

        return success;
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

    private void printTimeInfo(long cpuTime, long realTime,
                               int kompileSteps, int pdfSteps, int krunSteps) {
        String defInfo = String.format("Definitions kompiled: %s%n", kompileSteps);
        String pdfInfo = String.format("PDF posters kompiled: %s%n", pdfSteps);
        String krunInfo = String.format("Programs krun:        %s%n", krunSteps);
        String totalInfo = String.format(
                "Total time: %s'%s'' elapsed, %s'%s'' CPU%n",
                realTime / 60, realTime % 60,
                cpuTime / 60, cpuTime % 60);

        StringBuilder sb = new StringBuilder();
        sb.append("----------------------------\n");
        sb.append(defInfo).append(pdfInfo).append(krunInfo).append(totalInfo);
        sb.append("----------------------------\n");

        System.out.println(sb);
    }
}
