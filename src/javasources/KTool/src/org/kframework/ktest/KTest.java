package org.kframework.ktest;

import java.awt.Color;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.stream.*;
import javax.xml.transform.dom.*;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.io.FileUtils;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.Main;
import org.kframework.ktest.execution.Execution;
import org.kframework.ktest.execution.Task;
import org.kframework.ktest.tests.Program;
import org.kframework.ktest.tests.Test;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.OptionComparator;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.xml.sax.SAXException;

public class KTest {

    private static final String USAGE = "ktest <file> [options]";
    private static final String HEADER_STANDARD = "<file> is either a K definition (single job mode) or an XML configuration (batch mode).";
    private static final String FOOTER_STANDARD = "";
    private static final String HEADER_EXPERIMENTAL = "Experimental options:";
    private static final String FOOTER_EXPERIMENTAL = Main.FOOTER_EXPERIMENTAL;

    private static void printUsageS(KTestOptionsParser op) {
        org.kframework.utils.Error.helpMsg(USAGE, HEADER_STANDARD, FOOTER_STANDARD, op.getOptionsStandard(), new OptionComparator(op.getOptionList()));
    }
    private static void printUsageE(KTestOptionsParser op) {
        org.kframework.utils.Error.helpMsg(USAGE, HEADER_EXPERIMENTAL, FOOTER_EXPERIMENTAL, op.getOptionsExperimental(), new OptionComparator(op.getOptionList()));
    }

    public static void test(String[] args) {

        KTestOptionsParser op = new KTestOptionsParser();
        CommandLine cmd = op.parse(args);
        if (cmd == null) {
            printUsageS(op);
            System.exit(1);
        }

        // Help
        if (cmd.hasOption(Configuration.HELP_OPTION)) {
            printUsageS(op);
            System.exit(0);
        }
        if (cmd.hasOption(Configuration.HELP_EXPERIMENTAL_OPTION)) {
            printUsageE(op);
            System.exit(0);
        }

        // Version
        if (cmd.hasOption(Configuration.VERSION_OPTION)) {
            String msg = FileUtil.getFileContent(KPaths.getKBase(false)
                    + KPaths.VERSION_FILE);
            System.out.println(msg);
            System.exit(0);
        }

        // Dry run
        if (cmd.hasOption(Configuration.DRY_RUN_OPTION)) {
            Configuration.DRY_RUN = true;
            System.out.println("DRY: log=/tmp/ktest.`date +%Y_%m_%d_%H_%M_%S`; mkdir -p $log; trap \"rm -rf $log; exit\" SIGHUP SIGINT SIGTERM");
        }

        if (cmd.hasOption("debug")) {
            Configuration.DEBUG = true;
        }

        if (cmd.hasOption("ignore-white-spaces") && cmd.getOptionValue("ignore-white-spaces").equals("off")) {
            Configuration.IGNORE_WHITE_SPACES = false;
        }

        // Timeout
        if (cmd.hasOption(Configuration.TIMEOUT_OPTION)) {
            Configuration.KOMPILE_ALL_TIMEOUT = Long.parseLong(cmd.getOptionValue(Configuration.TIMEOUT_OPTION));
        }

        // Input argument
        String input = null;
        String[] remainingArgs = cmd.getArgs();
        if (remainingArgs.length < 1) {
            String msg = "You have to provide an input file, which is either a K definition (*.k) or a test configuration (*.xml).";
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
        } else if (remainingArgs.length > 1) {
            String msg = "You cannot provide more than one argument. You may miss a dash '-' or a quote '\"' for the options.";
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
        } else {
            input = remainingArgs[0];
        }
        // Single job mode
        if (input.endsWith(".k")) {
            Configuration.KDEF = input;
            Configuration.SINGLE_DEF_MODE = true;
            // Invalid: --directory
            if (cmd.hasOption(Configuration.DIRECTORY_OPTION)) {
                String msg = "You cannot use the --" + Configuration.DIRECTORY_OPTION + " option when a single K definition is given: " + Configuration.KDEF;
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
            }
            // Optional: --programs
            if (cmd.hasOption(Configuration.PROGRAMS_OPTION)) {
                Configuration.PGM_DIR = cmd.getOptionValue(Configuration.PROGRAMS_OPTION).trim();
                if (Configuration.PGM_DIR.equals("")) {
                    Configuration.PGM_DIR = null;
                }
            }
            // Optional: --results
            if (cmd.hasOption(Configuration.RESULTS_OPTION)) {
                Configuration.RESULTS_FOLDER = cmd.getOptionValue(Configuration.RESULTS_OPTION).trim();
                if (Configuration.RESULTS_FOLDER.equals("")) {
                    Configuration.RESULTS_FOLDER = null;
                }
            }
            // Optional: --extensions
            if (cmd.hasOption(Configuration.EXTENSIONS_OPTION)) {
                String extensionsOption = cmd.getOptionValue(Configuration.EXTENSIONS_OPTION).trim();
                if (!extensionsOption.equals("")) {
                    Configuration.EXTENSIONS = Arrays.asList(extensionsOption.split("\\s+"));
                }
            }
            // Required: all or nothing: --programs and --extensions
            if (Configuration.EXTENSIONS != null) {
                // --extensions without --programs
                if (Configuration.PGM_DIR == null) {
                    String msg = "The given --extensions option has no effect. You might miss a --programs option.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
                }
            } else {
                // --programs without --extensions
                if (Configuration.PGM_DIR != null) {
                    String msg = "You have to provide a list of extensions by using a --" + Configuration.EXTENSIONS_OPTION + " option, when the --" + Configuration.PROGRAMS_OPTION + " is given.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
                }
            }
        // Batch job mode
        } else if (input.endsWith(".xml")) {
            Configuration.CONFIG = input;
            Configuration.SINGLE_DEF_MODE = false;
            // Optional: --directory
            if (cmd.hasOption(Configuration.DIRECTORY_OPTION)) {
                Configuration.KDEF = cmd.getOptionValue(Configuration.DIRECTORY_OPTION);
                if (!new File(Configuration.KDEF).isDirectory()) {
                    String msg = "Invalid options: " + Configuration.KDEF + " is not a directory. You should provide a (root) directory where K definitions reside.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
                }
            }
            String inputDir = new File(input).getAbsoluteFile().getParent();
            // Optional: --programs
            if (cmd.hasOption(Configuration.PROGRAMS_OPTION)) {
                Configuration.PGM_DIR = cmd.getOptionValue(Configuration.PROGRAMS_OPTION).trim();
                org.kframework.utils.Error.checkIfInputDirectory(Configuration.PGM_DIR);
            } else {
                Configuration.PGM_DIR = inputDir;
            }
            // Optional: --results
            if (cmd.hasOption(Configuration.RESULTS_OPTION)) {
                Configuration.RESULTS_FOLDER = cmd.getOptionValue(Configuration.RESULTS_OPTION).trim();
                org.kframework.utils.Error.checkIfInputDirectory(Configuration.RESULTS_FOLDER);
            } else {
                Configuration.RESULTS_FOLDER = inputDir;
            }
            // Invalid: --extensions
            if (cmd.hasOption(Configuration.EXTENSIONS_OPTION)) {
                String msg = "You cannot use the --" + Configuration.EXTENSIONS_OPTION + " option when a test configuration is given: " + Configuration.CONFIG;
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
            }
            // Invalid: --exclude
            if (cmd.hasOption(Configuration.EXCLUDE_OPTION)) {
                String msg = "You cannot use the --" + Configuration.EXCLUDE_OPTION + " option when a test configuration is given: " + Configuration.CONFIG;
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
            }
        } else {
            String msg = "You have to provide a valid input file, which is either a K definition (*.k) or a test configuration (*.xml).";
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
        }

        // List of excluded programs
        if (cmd.hasOption(Configuration.EXCLUDE_OPTION)) {
            Configuration.EXCLUDE_PROGRAMS = Arrays.asList(cmd.getOptionValue(
                    Configuration.EXCLUDE_OPTION).split("\\s+"));
        }

        if (cmd.hasOption(Configuration.REPORT_OPTION)) {
            Configuration.REPORT = true;
        }

        // Resolve skip options
        if (cmd.hasOption(Configuration.SKIP_OPTION)) {
            String[] stepsToSkip = cmd
                    .getOptionValue(Configuration.SKIP_OPTION).split("\\s+");
            for (String step : stepsToSkip) {
                switch (step) {
                    case Configuration.KOMPILE_STEP:
                        Configuration.KOMPILE = false; break;
                    case Configuration.PDF_STEP:
                        Configuration.PDF = false; break;
                    case Configuration.PROGRAMS_STEP:
                        Configuration.PROGRAMS = false; break;
                }
            }
        }

        // Verbose
        if (cmd.hasOption(Configuration.VERBOSE_OPTION)) {
            Configuration.VERBOSE = true;
        }

        // Maximum number of threads
        if (cmd.hasOption(Configuration.PROCESSES_OPTION)) {
            Execution.POOL_SIZE = Integer.parseInt(cmd
                    .getOptionValue(Configuration.PROCESSES_OPTION));
        }

        // delete junit-reports dir
        try {
            FileUtils.deleteDirectory(new File(Configuration.JR));
        } catch (IOException e) {
            // silently ignore
        }

        // execution
        if (Configuration.SINGLE_DEF_MODE) {
            List<Test> alltests = new LinkedList<Test>();

            List<String> pgmsFolder = Configuration.PGM_DIR == null ? new LinkedList<String>()
                    : Arrays.asList(Configuration.PGM_DIR.split("\\s+"));
            List<String> resultsFolder = Configuration.RESULTS_FOLDER == null ? new LinkedList<String>()
                    : Arrays.asList(Configuration.RESULTS_FOLDER.split("\\s+"));
            List<String> extensions = Configuration.EXTENSIONS == null ? new LinkedList<String>() : Configuration.EXTENSIONS;
            Test test = new Test(Configuration.KDEF, pgmsFolder, resultsFolder,
                    extensions, Configuration.EXCLUDE_PROGRAMS,
                    System.getProperty("user.dir"));
            alltests.add(test);

            testing(0, new File(System.getProperty("user.dir")), alltests);
        } else {
            testConfig(Configuration.CONFIG, Configuration.KDEF,
                    Configuration.PGM_DIR, Configuration.RESULTS_FOLDER);
        }
    }

    private static void testConfig(String configFile, String rootDir,
            String rootProgramsDir, String rootResultsDir) {

        int exitCode = 0;
        List<Test> alltests = new LinkedList<Test>();

        // load config
        try {
            alltests = parseXMLConfig(configFile, rootDir, rootProgramsDir,
                    rootResultsDir);
        } catch (ParserConfigurationException e) {
            exitCode = 1;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.PARSER, e.getLocalizedMessage()));
        } catch (SAXException e) {
            exitCode = 1;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.PARSER, e.getLocalizedMessage()));
        } catch (IOException e) {
            exitCode = 1;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.PARSER, e.getLocalizedMessage()));
        }

        testing(exitCode, new File(System.getProperty("user.dir")), alltests);
    }

    private static List<Test> parseXMLConfig(String configFile,
            String rootDefDir, String rootProgramsDir, String rootResultsDir)
            throws ParserConfigurationException, SAXException, IOException {
        List<Test> alltests = new LinkedList<Test>();
        DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
        DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();

        if (!new File(configFile).exists()) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.CRITICAL, "File " + configFile
                            + " does not exists", "command line",
                    "System file."));
        }

        System.out.println("Buildfile: " + configFile);
      //Document doc = dBuilder.parse(new File(configFile));
        Document doc = dBuilder.newDocument();
        doc.appendChild(doc.createElement(Configuration.TESTS));
        addConfigW(doc, configFile, rootDefDir, rootProgramsDir, rootResultsDir);

        if (Configuration.DEBUG) {
          try {
            DOMSource source = new DOMSource(doc);
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            StreamResult result = new StreamResult(configFile + ".xml"); //System.out
            transformer.transform(source, result);
          } catch (Exception e) {
            e.printStackTrace();
          }
        }

        Element root = doc.getDocumentElement();

        if (!root.getTagName().equals(Configuration.TESTS)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Test configuration (XML) files must have <" + Configuration.TESTS + "> tag as root."));
        }

        NodeList test = root.getElementsByTagName(Configuration.TEST);
        for (int i = 0; i < test.getLength(); i++)
            alltests.add(new Test((Element) test.item(i), rootDefDir,
                    rootProgramsDir, rootResultsDir, System
                            .getProperty("user.dir")));

        return alltests;
    }

    private static void testing(int exitCode, File homeDir, List<Test> alltests) {
        List<Test> alltestsUnique = filterUniqueDefinition(alltests);

        exitCode |= resultKompile(execKompile(homeDir, alltestsUnique));
        exitCode |= resultPdf(execPdf(homeDir, alltestsUnique));
        exitCode |= execPrograms(homeDir, alltests);

        //GlobalSettings.kem.print();
        if (exitCode != 0)
            System.exit(exitCode);
    }

    private static List<Test> filterUniqueDefinition(List<Test> alltests) {
        List<Test> alltestsUnique = new LinkedList<Test>();
        try {
            Map<String, String> kompileOptionM = new HashMap<String, String>();
            Map<String, String>    definitionM = new HashMap<String, String>();
            for (Test test : alltests) {
                String definition = new File(test.getLanguage()).getCanonicalPath();
                String directory = new File(test.getDirectory()).getCanonicalPath();
                String kompileOption = test.getKompileOptions();
                String oldKompileOption = kompileOptionM.get(directory);
                String oldDefinition    =    definitionM.get(directory);
                // not duplicated
                if (oldKompileOption == null) {
                    alltestsUnique.add(test);
                }
                // sanitize
                if (oldKompileOption != null && !oldKompileOption.equals(kompileOption)) {
                    String msg = "There are multiple K definitions with different kompile options where they share the same directory: " + directory + ". ";
                    msg += "Two different options are ";
                    msg += "<test definition=" + oldDefinition + "; kompile-option=" + oldKompileOption + " /> and ";
                    msg += "<test definition=" +    definition + "; kompile-option=" +    kompileOption + " />.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
                } else {
                    kompileOptionM.put(directory, kompileOption);
                       definitionM.put(directory, definition);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
            String msg = "File.getCanonicalPath() failed.";
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, Configuration.wrap(msg), "command line", "System file."));
        }
        return alltestsUnique;
    }

    private static Map<Test, Task> execKompile(File homeDir, List<Test> alltests) {
        int i = 0, j = 0;
        wrapPrintStep("Kompile the language definitions...");
        Map<Test, Task> kompileTaskM = new TreeMap<Test, Task>();
        for (Test test : alltests) {
            if ((!test.isSkipKompile() && Configuration.KOMPILE)
                || !new File(test.getCompiled()).exists()) {
                Task def = test.getDefinitionTask(homeDir);
                kompileTaskM.put(test, def);
                wrapExecutionExecute(def);
                if (test.runOnOS()) {
                    Task unixOnlyScript = test.getUnixOnlyScriptTask(homeDir);
                    if (unixOnlyScript != null) {
                        wrapExecutionExecute(unixOnlyScript);
                    }
                }
                i++;
            } else {
                j++;
            }
        }
        System.out.println("(" + (i + j) + " in total)");
        if (j > 0)
            System.out.println("Skipped " + j + " definitions");
        if (i > 0)
            System.out.println("Compiling " + i + " definitions");
        wrapExecutionFinish();

        return kompileTaskM;
    }

    private static int resultKompile(Map<Test, Task> kompileTaskM) {
        int ret = 0;

        if (Configuration.KOMPILE) {
            if (!GlobalSettings.isWindowsOS()) {
                // report
                for (Entry<Test, Task> entry : kompileTaskM.entrySet()) {
                    entry.getKey().reportCompilation(entry.getValue());
                }
            }

            // console display
            String kompileStatus = "\n";
            for (Entry<Test, Task> entry : kompileTaskM.entrySet()) {
                if (!entry.getKey().compiled(entry.getValue())) {
                    kompileStatus += ColorUtil.RgbToAnsi(Color.red, ColorSetting.ON) + "FAIL: "
                            + entry.getKey().getLanguage()
                            + ColorUtil.ANSI_NORMAL + "\n";
                    ret = 1;
                }
            }
            if (kompileStatus.equals("\n"))
                kompileStatus = "SUCCESS";
            System.out.println(kompileStatus);
        } else {
            System.out.println("Done.");
        }

        return ret;
    }

    private static Map<Test, Task> execPdf(File homeDir, List<Test> alltests) {
        int i = 0, j = 0;
        wrapPrintStep("Generating PDF documentation...");
        Map<Test, Task> pdfTaskM = new TreeMap<Test, Task>();
        for (Test test : alltests) {
            if (!test.isSkipPdf() && Configuration.PDF){
                Task pdfDef = test.getPdfDefinitionTask(homeDir);
                pdfTaskM.put(test, pdfDef);
                wrapExecutionExecute(pdfDef);
                i++;
            } else {
                j++;
            }
        }
        System.out.println("(" + (i + j) + " in total)");
        if (j > 0)
            System.out.println("Skipped " + j + " definitions");
        if (i > 0)
            System.out.println("Generate pdf for " + i + " definitions");
        wrapExecutionFinish();
        return pdfTaskM;
    }

    private static int resultPdf(Map<Test, Task> pdfTaskM) {
        int ret = 0;

        if (Configuration.PDF) {

            if (!GlobalSettings.isWindowsOS()) {
                // create XML report
                for (Entry<Test, Task> entry : pdfTaskM.entrySet()) {
                    entry.getKey().reportPdfCompilation(entry.getValue());
                }
            }
            // console messages
            String pdfKompileStatus = "\n";
            for (Entry<Test, Task> entry : pdfTaskM.entrySet()) {
                if (!entry.getKey().compiledPdf(entry.getValue())) {
                    pdfKompileStatus += ColorUtil.RgbToAnsi(Color.red, ColorSetting.ON)
                            + "FAIL: " + entry.getKey().getLanguage()
                            + ColorUtil.ANSI_NORMAL + "\n";
                    ret = 1;
                }
            }
            if (pdfKompileStatus.equals("\n"))
                pdfKompileStatus = "SUCCESS";
            System.out.println(pdfKompileStatus);
        } else {
            System.out.println("Done.");
        }

        return ret;
    }

    private static int execPrograms(File homeDir, List<Test> alltests) {
        int ret = 0;
        // execute all programs (for which corresponding definitions are
        // compiled)
        for (Test test : alltests) {
            if (!test.isSkipPrograms() && Configuration.PROGRAMS){
                if (test.runOnOS()) {
                    wrapPrintStep("Running " + test.getLanguage() + " programs... " + test.getTag());

                    // execute
                    List<Program> pgms = test.getPrograms();
                    Map<Program, Task> all = new TreeMap<Program, Task>();

                    // total programs counter
                    int i = 0;
                    // i/o counters
                    int in = 0;
                    int out = 0;

                    for (Program p : pgms) {
                        Task task = p.getTask(homeDir);
                        all.put(p, task);
                        if (Configuration.PROGRAMS) {
                            wrapExecutionExecute(task);
                        }
                        i++;
                        if (p.hasInput()) in++;
                        if (p.hasOutput()) out++;
                    }
                    if (Configuration.PROGRAMS) {
                        System.out.println("(" + i + " in total, " + in + " with input, " + out + " with output)");
                    } else {
                        System.out.println("\nSkipped " + i + " programs");
                    }
                    wrapExecutionFinish();

                    if (Configuration.PROGRAMS) {

                        if (!GlobalSettings.isWindowsOS()) {
                            // report
                            for (Entry<Program, Task> entry : all.entrySet()) {
                                entry.getKey().reportTest(entry.getValue());
                            }
                        }

                        // console
                        String pgmOut = "";
                        for (Entry<Program, Task> entry : all.entrySet()) {
                            if (!entry.getKey().success(entry.getValue())) {
                                pgmOut += ColorUtil.RgbToAnsi(Color.red, ColorSetting.ON) + "FAIL: "
                                        + entry.getKey().getProgramPath()
                                        + ColorUtil.ANSI_NORMAL + "\n";
                                ret = 1;
                            }
                        }
                        if (pgmOut.equals(""))
                            pgmOut = "SUCCESS";
                        System.out.println(pgmOut);
                    }
                }
            } else {
                System.out.println("Skipped " + test.getLanguage() + " programs.");
            }
        }

        return ret;
    }

    private static void wrapExecutionExecute(Task task) {
        if (Configuration.DRY_RUN) {
            //System.out.println("DRY: " + task.getCommand());
            System.out.println("DRY: p[$LINENO]=$!; " + task.getCommand() + " >$log/$LINENO.out 2>$log/$LINENO.err || echo \"Failed: $LINENO\" &");
        } else {
            Execution.execute(task);
        }
    }
    private static void wrapExecutionFinish() {
        if (Configuration.DRY_RUN) {
            System.out.println("DRY: p[$LINENO]=$!; echo \"wait ${p[@]}\"; wait ${p[@]}");
        } else {
            Execution.finish();
        }
    }
    private static void wrapPrintStep(String step) {
        if (Configuration.DRY_RUN) {
            System.out.println(step);
            System.out.println("DRY: echo \"" + step + "\" &");
        } else {
            System.out.print(step);
        }
    }

    private static void addConfigW(Document destDoc, String configFile, String rootDefinition, String rootPrograms, String rootResults)
        throws IOException, SAXException, ParserConfigurationException {
        configFile     = makeAbsolutePath(Configuration.USER_DIR, configFile);
        rootDefinition = makeAbsolutePath(Configuration.USER_DIR, rootDefinition);
        rootPrograms   = makeAbsolutePath(Configuration.USER_DIR, rootPrograms);
        rootResults    = makeAbsolutePath(Configuration.USER_DIR, rootResults);
        addConfig(destDoc, configFile, rootDefinition, rootPrograms, rootResults, "", "", null);
    }
    private static void addConfig(Document destDoc, String configFile, String rootDefinition, String rootPrograms, String rootResults, String morePrograms, String moreResults, String exclude)
      throws IOException, SAXException, ParserConfigurationException {
        addConfigSanitize(destDoc, configFile, rootDefinition, rootPrograms, rootResults);
        Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().parse(configFile);
        Element root = doc.getDocumentElement();
        NodeList nodeList = root.getChildNodes();
        for (int i = 0; i < nodeList.getLength(); ++i) {
            Node node = nodeList.item(i);
            if (node.getNodeType() == Node.ELEMENT_NODE) {
                Element elem = (Element) node;
                if (elem.getTagName().equals("test")) {
                    Element test = (Element) destDoc.importNode(elem,true);
                    if (test.hasAttribute(Configuration.LANGUAGE)) {
                        test.setAttribute(Configuration.LANGUAGE,  makeAbsolutePath(rootDefinition, test.getAttribute(Configuration.LANGUAGE)));
                    } else {
                        String msg = "The attribute '" + Configuration.LANGUAGE + "' is required.";
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", "System file."));
                    }
                    String defDir = dirname(test.getAttribute(Configuration.LANGUAGE));
                    if (test.hasAttribute(Configuration.DIRECTORY)) {
                        test.setAttribute(Configuration.DIRECTORY, makeAbsolutePath(defDir, test.getAttribute(Configuration.DIRECTORY)));
                    } else {
                        test.setAttribute(Configuration.DIRECTORY, defDir);
                    }
                    // NOTE: if 'programs' or 'results' are not given, they are replaced with 'programs=""' or 'results=""'.
                    test.setAttribute(Configuration.PROGRAMS_DIR, makeAbsolutePaths(rootPrograms, test.getAttribute(Configuration.PROGRAMS_DIR)) + " " + morePrograms);
                    test.setAttribute(Configuration.RESULTS,      makeAbsolutePaths(rootResults,  test.getAttribute(Configuration.RESULTS))      + " " + moreResults);
                    if (exclude != null) { test.setAttribute(Configuration.EXCLUDE, exclude); }
                    destDoc.getDocumentElement().appendChild(test);
                } else if (elem.getTagName().equals(Configuration.INCLUDE)) {
                    String configFileDir = dirname(configFile);
                    String newConfigFile = null;
                    if (elem.hasAttribute(Configuration.CONFIG_FILE)) {
                        newConfigFile = makeAbsolutePath(configFileDir, elem.getAttribute(Configuration.CONFIG_FILE));
                    } else {
                        String msg = "An element '" + Configuration.INCLUDE + "' requires a '" + Configuration.CONFIG_FILE + "' attribute.";
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", "System file."));
                    }
                    String newRootDefinition = rootDefinition;
                    String newRootPrograms   = dirname(newConfigFile);
                    String newRootResults    = dirname(newConfigFile);
                    if (elem.hasAttribute(Configuration.DEFINITION_DIR))  { newRootDefinition = makeAbsolutePath(rootDefinition, elem.getAttribute(Configuration.DEFINITION_DIR)); }
                    if (elem.hasAttribute(Configuration.ROOT_PROGRAMS))   { newRootPrograms   = makeAbsolutePath(rootPrograms,   elem.getAttribute(Configuration.ROOT_PROGRAMS));  }
                    if (elem.hasAttribute(Configuration.ROOT_RESULTS))    { newRootResults    = makeAbsolutePath(rootResults,    elem.getAttribute(Configuration.ROOT_RESULTS));   }
                    String newMorePrograms = makeAbsolutePaths(rootPrograms, elem.getAttribute(Configuration.MORE_PROGRAMS)) + " " + morePrograms;
                    String newMoreResults  = makeAbsolutePaths(rootResults,  elem.getAttribute(Configuration.MORE_RESULTS))  + " " + moreResults;
                    String newExclude = exclude;
                    if (elem.hasAttribute(Configuration.EXCLUDE)) { newExclude = elem.getAttribute(Configuration.EXCLUDE); }
                    addConfig(destDoc, newConfigFile, newRootDefinition, newRootPrograms, newRootResults, newMorePrograms, newMoreResults, newExclude);
                } else {
                    String msg = "Invalid element name in the configuration file: " + elem.getTagName();
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", "System file."));
                }
            }
        }
    }
    private static void addConfigSanitize(Document destDoc, String configFile, String rootDefinition, String rootPrograms, String rootResults) {
        if (!new File(configFile).exists()) {
            String msg = "The configuration file does not exists.";
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, configFile, "System file."));
        }
        org.kframework.utils.Error.checkIfInputDirectory(rootDefinition);
        org.kframework.utils.Error.checkIfInputDirectory(rootPrograms);
        org.kframework.utils.Error.checkIfInputDirectory(rootResults);
    }

    private static String makeAbsolutePaths(String root, String dirs) {
        String resultDirs = "";
        List<String> dirL = Arrays.asList(dirs.trim().split("\\s+"));
        if (dirL.size() > 0) {
            for (String dir : dirL) {
                if (dir != null && !dir.equals("")) {
                    resultDirs = resultDirs + " " + makeAbsolutePath(root, dir.trim());
                }
            }
        }
        return resultDirs.trim();
    }

    private static String makeAbsolutePath(String root, String dir) {
        if (!new File(root).isAbsolute()) {
            String msg = "Internal Errors: Not a root: " + root;
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, "command line", "System file."));
        }
        String resultDir;
        if (new File(dir).isAbsolute()) {
            resultDir = dir;
        } else {
            resultDir = root + Configuration.FILE_SEPARATOR + dir;
        }
        try {
            return new File(resultDir).getCanonicalPath();
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    private static String dirname(String path) {
        return new File(path).getAbsoluteFile().getParent();
    }

}
