package org.kframework.ktest;

import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.ParseException;
import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.CmdArgs.CmdArg;
import org.kframework.ktest.CmdArgs.CmdArgParser;
import org.kframework.ktest.CmdArgs.Constants;
import org.kframework.ktest.CmdArgs.InvalidArgumentException;
import org.kframework.ktest.Config.ConfigFileParser;
import org.kframework.ktest.Config.InvalidConfigError;
import org.kframework.ktest.Config.LocationData;
import org.kframework.ktest.Test.TestCase;
import org.kframework.ktest.Test.TestSuite;
import org.kframework.utils.OptionComparator;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import java.io.File;
import java.io.IOException;
import java.util.*;


public class KTest {

    private final CmdArgParser argParser;

    private KTest(String[] args) throws ParseException {
        argParser = new CmdArgParser(args);
    }

    public int run() throws InvalidArgumentException, IOException, SAXException,
            ParserConfigurationException, InterruptedException, InvalidConfigError,
            TransformerException {
        if (argParser.cmdOpts.hasOption(Constants.HELP_OPTION))
            printHelpMsg();
        else if (argParser.cmdOpts.hasOption(Constants.VERSION_OPTION))
            printVersion();
        else {
            CmdArg cmdArgs = CmdArg.validateArgs(argParser.cmdOpts);
            TestSuite testSuite = makeTestSuite(cmdArgs.getTargetFile(), cmdArgs);
            if (cmdArgs.getDry())
                testSuite.dryRun();
            else
                return (testSuite.run() ? 0 : 1);
        }
        return 0;
    }

    private TestSuite makeTestSuite(String targetFile, CmdArg cmdArgs) throws SAXException,
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

    private void printHelpMsg() {
        HelpFormatter helpFormatter = new HelpFormatter();
        helpFormatter.setWidth(79);

        final String usage = "ktest <file> [options]";
        final String header = "<file> is either a K definition (single job mode) or an XML " +
                "configuration (batch mode).";
        final String footer = "";

        org.kframework.utils.Error.helpMsg(usage, header, footer, argParser.getOptions(),
                new OptionComparator(argParser.getOptionList()));
    }

    private void printVersion() {
        System.out.println(FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE));
    }

    public static void main(String[] args) {
        try {
            System.exit(new KTest(args).run());
        } catch (ParseException | InvalidArgumentException | SAXException |
                ParserConfigurationException | IOException | InterruptedException |
                TransformerException e) {
            e.printStackTrace();
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            e.getMessage(), "command line", "System file."));
        } catch (InvalidConfigError e) {
            LocationData location = e.getLocation();
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            e.getMessage(), location.getSystemId(), location.getPosStr()));
        }
        System.exit(1);
    }
}
