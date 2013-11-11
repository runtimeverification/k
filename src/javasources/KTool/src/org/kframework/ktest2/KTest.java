package org.kframework.ktest2;

import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.ParseException;
import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest2.CmdArgs.CmdArg;
import org.kframework.ktest2.CmdArgs.CmdArgParser;
import org.kframework.ktest2.CmdArgs.Constants;
import org.kframework.ktest2.CmdArgs.InvalidArgumentException;
import org.kframework.ktest2.Config.ConfigFileError;
import org.kframework.ktest2.Config.ConfigFileParser;
import org.kframework.ktest2.Config.InvalidConfigError;
import org.kframework.ktest2.Test.TestCase;
import org.kframework.ktest2.Test.TestSuite;
import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import java.io.File;
import java.io.IOException;


public class KTest {

    private final CmdArgParser argParser;

    private KTest(String[] args) throws ParseException {
        argParser = new CmdArgParser(args);
    }

    public void run() throws InvalidArgumentException, IOException, SAXException,
            ParserConfigurationException, ConfigFileError, InterruptedException, InvalidConfigError {
        if (argParser.cmdOpts.hasOption(Constants.HELP_OPTION))
            printHelpMsg();
        else if (argParser.cmdOpts.hasOption(Constants.VERSION_OPTION))
            printVersion();
        else {
            CmdArg cmdArgs = CmdArg.validateArgs(argParser.cmdOpts);
            TestSuite tests;
            switch (FilenameUtils.getExtension(cmdArgs.targetFile)) {
                case "xml":
                    tests = new TestSuite(
                                new ConfigFileParser(new File(cmdArgs.targetFile),
                                        cmdArgs).parse(),
                                cmdArgs.skips, cmdArgs.verbose, cmdArgs.timeout);
                    break;
                case "k":
                    tests = new TestSuite(TestCase.makeTestCaseFromK(cmdArgs),
                                cmdArgs.skips, cmdArgs.verbose, cmdArgs.timeout);
                    break;
                default:
                    // this code should be unreacable, because `validateArgs' should ensure that
                    // targetFile extension can only be .k or .xml
                    tests = null; assert false;
            }
            System.out.println(tests.run() ? "SUCCESS" : "FAIL");
        }
    }

    private void printHelpMsg() {
        // TODO: sort options as in kframework.ktest
        HelpFormatter helpFormatter = new HelpFormatter();
        helpFormatter.setWidth(79);

        final String usage = "ktest <file> [options]";
        final String header = "<file> is either a K definition (single job mode) or an XML " +
                "configuration (batch mode).";
        final String footer = "";

        helpFormatter.printHelp(usage, header, argParser.options, footer);
    }

    private void printVersion() {
        System.out.println("2");
    }

    public static void main(String[] args) {
        try {
            new KTest(args).run();
        } catch (ParseException | InvalidArgumentException | SAXException |
                ParserConfigurationException | IOException | ConfigFileError |
                InterruptedException | InvalidConfigError e) {
            System.out.println(e.getMessage());
            System.exit(1);
        }
    }
}
