// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.ktest.Config.ConfigFileParser;
import org.kframework.ktest.Config.InvalidConfigError;
import org.kframework.ktest.Config.LocationData;
import org.kframework.ktest.Test.TestCase;
import org.kframework.ktest.Test.TestSuite;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.CommonModule;
import org.xml.sax.SAXException;

import com.beust.jcommander.ParameterException;
import com.google.inject.Inject;
import com.google.inject.Module;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import java.io.File;
import java.io.IOException;
import java.util.*;


public class KTestFrontEnd extends FrontEnd {

    public static Module[] getModules(String[] args) {
        try {
            KTestOptions options = new KTestOptions();

            return new Module[] {
                    new KTestModule(options),
                    new JCommanderModule(args),
                    new CommonModule() };
        } catch (ParameterException ex) {
            printBootError(ex.getMessage());
            return null;
        }
    }

    private final KTestOptions options;
    private final KExceptionManager kem;

    @Inject
    KTestFrontEnd(
            KTestOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            JarInfo jarInfo) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo);
        this.options = options;
        this.kem = kem;
    }

    public boolean run() {
        try {
            options.validateArgs();
            TestSuite testSuite = makeTestSuite(options.getTargetFile(), options);
            if (options.getDry()) {
                testSuite.dryRun();
                return true;
            } else {
                return testSuite.run();
            }
        } catch (SAXException | ParserConfigurationException | IOException | InterruptedException |
                TransformerException | ParameterException e) {
            kem.registerCriticalError(e.getMessage(), e);
            return false;
        } catch (InvalidConfigError e) {
            LocationData location = e.getLocation();
            kem.registerCriticalError(e.getMessage(), e, location.getLocation(), location.getSource());
            return false;
        }
    }

    private TestSuite makeTestSuite(String targetFile, KTestOptions cmdArgs) throws SAXException,
            TransformerException, ParserConfigurationException, IOException, InvalidConfigError {
        TestSuite ret;
        switch (FilenameUtils.getExtension(targetFile)) {
        case "xml":
            ret = new TestSuite(new ConfigFileParser(
                    new File(cmdArgs.getTargetFile()), cmdArgs).parse(), cmdArgs);
            break;
        case "k":
            TestCase tc = TestCase.makeTestCaseFromK(cmdArgs);
            tc.validate();
            List<TestCase> tcs = new LinkedList<>();
            tcs.add(tc);
            ret = new TestSuite(tcs, cmdArgs);
            break;
        default:
            // this code should be unreacable, because `validateArgs' should ensure that
            // targetFile extension can only be .k or .xml
            ret = null; assert false;
        }
        return ret;
    }
}
