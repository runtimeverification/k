// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.ktest.CmdArgs.InvalidArgumentException;
import org.kframework.ktest.Config.ConfigFileParser;
import org.kframework.ktest.Config.InvalidConfigError;
import org.kframework.ktest.Config.LocationData;
import org.kframework.ktest.Test.TestCase;
import org.kframework.ktest.Test.TestSuite;
import org.kframework.utils.StringUtil;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.options.SortedParameterDescriptions;
import org.xml.sax.SAXException;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import java.io.File;
import java.io.IOException;
import java.util.*;


public class KTest {

    private final KTestOptions options;

    public KTest(KTestOptions options) {
        this.options = options;
    }

    public boolean run() throws InvalidArgumentException, IOException, SAXException,
            ParserConfigurationException, InterruptedException, InvalidConfigError,
            TransformerException {


        options.validateArgs();
        TestSuite testSuite = makeTestSuite(options.getTargetFile(), options);
        if (options.getDry()) {
            testSuite.dryRun();
            return true;
        } else {
            return testSuite.run();
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

    /**
     *
     * @param args command line arguments
     * @return true if the application terminated normally; false otherwise
     */
    public static boolean main(String[] args) {
        KTestOptions options = new KTestOptions();
        options.getGlobal().initialize();
        try {
            JCommander jc = new JCommander(options, args);
            jc.setProgramName("ktest");
            jc.setParameterDescriptionComparator(new SortedParameterDescriptions());

            if (options.getGlobal().help) {
                StringBuilder sb = new StringBuilder();
                jc.usage(sb);
                System.out.print(StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0]);
                return true;
            }

            if (options.getGlobal().version) {
                String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.print(msg);
                return true;
            }
            KTest ktest = new KTest(options);

            return ktest.run();
        } catch (SAXException | ParserConfigurationException | IOException | InterruptedException |
                TransformerException | InvalidArgumentException | ParameterException e) {
            GlobalSettings.kem.registerCriticalError(e.getMessage(), e);
        } catch (InvalidConfigError e) {
            LocationData location = e.getLocation();
            GlobalSettings.kem.registerCriticalError(e.getMessage(), e, location);
        }
        return false;
    }
}
