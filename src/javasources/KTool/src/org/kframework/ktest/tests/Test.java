package org.kframework.ktest.tests;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.kframework.ktest.Configuration;
import org.kframework.ktest.execution.Task;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class Test implements Comparable<Test> {

    /* data read from config.xml */
    private String language;
    private List<String> programsFolders;
    private List<String> resultsFolders;
    private String tag = "";
    private String unixOnlyScript;
    private boolean recursive;
    private List<String> extensions;
    private List<String> excludePrograms;
    private Map<String, String> kompileOptions = new HashMap<String, String>();
    private Map<String, String> generalKrunOptions = new HashMap<String, String>();
    private List<Program> specialPrograms = new LinkedList<Program>();
    private boolean skipPdf;
    private boolean skipKompile;
    private boolean skipPrograms;

    /* data needed for temporary stuff */
    private Document doc;
    public Element report;
    private List<Program> programs;
    private String reportDir = null;

    public Test(String language, List<String> programsFolder,
            List<String> resultsFolder, List<String> extensions,
            List<String> excludePrograms, String homeDir) {
        this.language = language;
        this.programsFolders = programsFolder;
        this.resultsFolders = resultsFolder;
        this.extensions = extensions;
        this.excludePrograms = excludePrograms == null ? new LinkedList<String>()
                : excludePrograms;
        this.recursive = true;
        this.unixOnlyScript = null;

        // reports
        try {
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db = dbf.newDocumentBuilder();
            doc = db.newDocument();
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
        }

        report = getInitialElement(language);
        doc.appendChild(report);

        // general krun options
        generalKrunOptions.put("--output-mode", "none");
        generalKrunOptions.put("--color", "off");

        initializePrograms(homeDir);
    }

    public Test(Element test, String rootDefDir, String rootProgramsDir,
            String rootResultsDir, String homeDir) {

        init(test, rootDefDir, rootProgramsDir, rootResultsDir);

        // reports
        try {
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db = dbf.newDocumentBuilder();
            doc = db.newDocument();
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
        }

        report = getInitialElement(language);
        doc.appendChild(report);

        initializePrograms(homeDir);
    }

    private void initializePrograms(String homeDir) {
        programs = new LinkedList<Program>();

        // check the existence of the results folder
        if (resultsFolders != null) {
            for (String rf : resultsFolders)
                if (rf != null && !rf.equals("") && !new File(rf).exists()) {
                    GlobalSettings.kem.register(new KException(
                            ExceptionType.WARNING, KExceptionGroup.CRITICAL,
                            "Result folder " + rf + " does not exists.",
                            "command line", "System file."));
                }

        }

        for (String programsFolder : programsFolders) {

            if (!programsFolder.equals("")
                    && !new File(programsFolder).exists()) {
                GlobalSettings.kem.register(new KException(
                        ExceptionType.WARNING, KExceptionGroup.CRITICAL,
                        "Programs folder " + programsFolder
                                + " does not exists.", "command line",
                        "System file."));
            }

            if (programsFolder == null || programsFolder.equals(""))
                return;

            List<String> allProgramPaths = searchAll(programsFolder,
                    extensions, recursive);

            for (String programPath : allProgramPaths) {
                // ignore the programs from exclude list
                boolean excluded = false;
                for (String exclude : excludePrograms)
                    if (!exclude.equals("") && programPath.contains(exclude))
                        excluded = true;
                if (excluded)
                    continue;

                Map<String, String> krunOptions = null;
                boolean special = false;
                // treat special programs
                for (Program p : specialPrograms) {
                    if (p.programPath.equals(programPath)) {
                        krunOptions = p.krunOptions;
                        special = true;
                        continue;
                    }
                }
                if (!special)
                    krunOptions = this.generalKrunOptions;

                String input = null;
                String output = null;
                String error = null;
                if (resultsFolders != null) {
                    for (String rf : resultsFolders) {
                        String inputFile = searchInputFile(rf, new File(
                                programPath).getName(), recursive);
                        input = getFileAsStringOrNull(inputFile);

                        String outputFile = searchOutputFile(rf, new File(
                                programPath).getName(), recursive);
                        output = getFileAsStringOrNull(outputFile);

                        String errorFile = searchErrorFile(rf, new File(
                                programPath).getName(), recursive);
                        error = getFileAsStringOrNull(errorFile);

                        if (input != null || output != null || error != null) {
                            break;
                        }
                    }
                }

                // custom programPath
                if (!GlobalSettings.isWindowsOS()) {
                    programPath = programPath.replaceFirst(homeDir
                            + Configuration.FILE_SEPARATOR, "");
                } 
                Program p = new Program(programPath, krunOptions, this, input,
                        output, error);
                programs.add(p);

            }
        }
    }

    private String getFileAsStringOrNull(String file) {
        String fileAsString = null;
        if (file != null)
            try {
                fileAsString = Task.readString(new FileInputStream(file));
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
        return fileAsString;
    }

    private String searchOutputFile(String resultsFolder2, String name,
            boolean recursive2) {
        return searchFile(resultsFolder2, name + Configuration.OUT, recursive);
    }

    private String searchErrorFile(String resultsFolder2, String name,
            boolean recursive2) {
        return searchFile(resultsFolder2, name + Configuration.ERR, recursive);
    }

    private String searchInputFile(String resultsFolder2, String name,
            boolean recursive) {
        return searchFile(resultsFolder2, name + Configuration.IN, recursive);
    }

    private String searchFile(String folder, String filename, boolean recursive) {
        String[] files = new File(folder).list();
        String file = null;
        if (files != null)
            for (int i = 0; i < files.length; i++) {

                // search in depth first
                if (recursive)
                    if (new File(folder + Configuration.FILE_SEPARATOR
                            + files[i]).isDirectory())
                        file = searchFile(folder + Configuration.FILE_SEPARATOR
                                + files[i], filename, recursive);
                if (file != null)
                    return file;

                if (new File(folder + Configuration.FILE_SEPARATOR + files[i])
                        .isFile())
                    if (files[i].equals(filename))
                        file = new File(folder + Configuration.FILE_SEPARATOR
                                + files[i]).getAbsolutePath();
                if (file != null)
                    return file;
            }

        return file;
    }

    private List<String> searchAll(String programsFolder,
            List<String> extensions, boolean recursive) {

        if (extensions.isEmpty())
            return new LinkedList<String>();

        List<String> paths = new LinkedList<String>();
        for (String extension : extensions)
            paths.addAll(searchAll(programsFolder, extension));

        if (recursive) {
            String[] files = new File(programsFolder).list();
            if (files != null)
                for (int i = 0; i < files.length; i++) {
                    if (new File(programsFolder + Configuration.FILE_SEPARATOR
                            + files[i]).isDirectory()) {
                        paths.addAll(searchAll(programsFolder
                                + Configuration.FILE_SEPARATOR + files[i],
                                extensions, recursive));
                    }
                }
        }

        return paths;
    }

    private List<String> searchAll(String programsFolder2, String extension) {
        String[] files = new File(programsFolder2).list();
        List<String> fls = new LinkedList<String>();
        if (files != null) {
            for (int i = 0; i < files.length; i++)
                if (new File(programsFolder2 + Configuration.FILE_SEPARATOR
                        + files[i]).isFile()) {
                    if (files[i].endsWith(extension))
                        fls.add(programsFolder2 + Configuration.FILE_SEPARATOR
                                + files[i]);
                }
        }
        return fls;
    }

    private void init(Element test, String rootDefDir, String rootProgramsDir,
            String rootResultsDir) {
        // get full name
        language = resolveAbsolutePathRelativeTo(
                test.getAttribute(Configuration.LANGUAGE), rootDefDir,
                Configuration.DEF_ERROR);

        // get programs dir
        List<String> allpd = Arrays.asList(test.getAttribute(
                Configuration.PROGRAMS_DIR).split("\\s+"));
        if (allpd.size() > 0) {
            programsFolders = new LinkedList<String>();
            resultsFolders = new LinkedList<String>();
            for (String pd : allpd) {
                if (pd != null && !pd.equals("")) {
                    String p = resolveAbsolutePathRelativeTo(pd.trim(),
                            rootProgramsDir, Configuration.PGM_ERROR);
                    if (p != null){
                        programsFolders.add(p);
                        // also add this program folder as default result folder
                        resultsFolders.add(p);
                    }
                }
            }
        }

        // get tests results
        List<String> allrd = new LinkedList<String>();
        if (test.hasAttribute(Configuration.RESULTS))
                allrd = Arrays.asList(test.getAttribute(Configuration.RESULTS).split("\\s+"));
        if (allrd.size() > 0) {
            // reset the default results folder if Configuration.RESULTS is given
            resultsFolders = new LinkedList<String>();
            for (String rd : allrd)
                if (rd != null && !rd.equals("")) {
                    String p = resolveAbsolutePathRelativeTo(rd.trim(),
                            rootResultsDir, Configuration.RES_ERROR);
                    if (p != null)
                        resultsFolders.add(p);
                }
        } else if (resultsFolders.size() == 0)
            resultsFolders = null;

        // get report dir
        reportDir = resolveAbsolutePathRelativeTo(
                test.getAttribute(Configuration.REPORT_DIR), rootDefDir, "");
        if (report != null && reportDir.equals(""))
            reportDir = null;

        unixOnlyScript = test.getAttribute(Configuration.UNIX_ONLY);
        if (unixOnlyScript.equals(""))
            unixOnlyScript = null;

        // get Jenkins tag
        tag = test.getAttribute(Configuration.TITLE);

        // get skip
        if (test.hasAttribute(Configuration.SKIP_OPTION)) {
            String skip = test.getAttribute(Configuration.SKIP_OPTION);
            if (skip.contains(Configuration.KOMPILE_STEP))
                this.skipKompile = true;
            if (skip.contains(Configuration.PDF_STEP))
                this.skipPdf = true;
            if (skip.contains(Configuration.PROGRAMS_STEP))
                this.skipPrograms = true;
        }

        // set recursive
        String rec = test.getAttribute(Configuration.RECURSIVE);
        if (rec.equals("") || rec.equals(Configuration.YES))
            recursive = true;
        else
            recursive = false;

        // extensions
        extensions = Arrays.asList(test.getAttribute(Configuration.EXTENSIONS2)
                .split("\\s+"));

        // exclude programs
        excludePrograms = Arrays.asList(test
                .getAttribute(Configuration.EXCLUDE).split("\\s+"));

        // kompile options
        NodeList kompileOpts = test
                .getElementsByTagName(Configuration.KOMPILE_OPTION);
        for (int i = 0; i < kompileOpts.getLength(); i++) {
            Element option = (Element) kompileOpts.item(i);
            kompileOptions.put(option.getAttribute(Configuration.NAME),
                    option.getAttribute(Configuration.VALUE));
        }

        // load programs with special krun options
        NodeList specialPgms = test.getElementsByTagName(Configuration.PROGRAM);
        for (int i = 0; i < specialPgms.getLength(); i++) {
            Element pgm = (Element) specialPgms.item(i);
            String programPath = pgm.getAttribute(Configuration.NAME);
            Map<String, String> map = getKrunOptions(pgm);
            String input = null;
            String output = null;
            String error = null;
            if (resultsFolders != null) {
                for (String rf : resultsFolders) {
                    String inputFile = searchInputFile(rf,
                            new File(programPath).getName(), recursive);
                    input = getFileAsStringOrNull(inputFile);

                    String outputFile = searchOutputFile(rf, new File(
                            programPath).getName(), recursive);
                    output = getFileAsStringOrNull(outputFile);

                    String errorFile = searchErrorFile(rf,
                            new File(programPath).getName(), recursive);
                    error = getFileAsStringOrNull(errorFile);

                    if (input != null || output != null || error != null) {
                        break;
                    }
                }
            }

            Program program = new Program(resolveAbsolutePathRelativeTo(
                    programPath, rootProgramsDir, Configuration.PGM_ERROR),
                    map, this, input, output, error);
            specialPrograms.add(program);
        }

        // general krun options
        NodeList genOpts = test
                .getElementsByTagName(Configuration.ALL_PROGRAMS);
        if (genOpts != null && genOpts.getLength() > 0) {
            Element all = (Element) genOpts.item(0);
            generalKrunOptions = getKrunOptions(all);
        }

        if (genOpts.getLength() == 0) {
            generalKrunOptions.put("--color", "off");
            generalKrunOptions.put("--output-mode", "none");
        }
    }

    private String resolveAbsolutePathRelativeTo(String path, String rootDir,
            String errorMessage) {

        if (path == null) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.CRITICAL,
                    "Empty attribute in configuration file.", "command line",
                    "System file."));
        }

        if (new File(path).isAbsolute())
            return new File(path).getAbsolutePath();
        else {

            if (rootDir == null) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "File " + rootDir
                                + " does not exists.", "command line",
                        "System file."));
            }

            if (new File(rootDir + Configuration.FILE_SEPARATOR + path)
                    .exists()) {
                return new File(rootDir + Configuration.FILE_SEPARATOR + path)
                        .getAbsolutePath();
            } else
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL, "File " + rootDir
                                + Configuration.FILE_SEPARATOR + path
                                + " does not exists.\n" + errorMessage,
                        "command line", "System file."));
        }
        return null;
    }

    private Map<String, String> getKrunOptions(Element parent) {
        Map<String, String> map = new HashMap<String, String>();
        NodeList opts = parent.getElementsByTagName(Configuration.KRUN_OPTION);
        for (int j = 0; j < opts.getLength(); j++) {
            Element krunOpt = (Element) opts.item(j);

            // unescape < and >
            String optValue = krunOpt.getAttribute(Configuration.VALUE);
            optValue = optValue.replaceAll("&lt;", "<");
            optValue = optValue.replaceAll("&gt;", ">");

            String parserHome = krunOpt.getAttribute(Configuration.PARSER_HOME);
            String parser = System.getenv(parserHome);
            if (parser != null) {
                optValue = parser + System.getProperty("file.separator")
                        + optValue;
            }

            map.put(krunOpt.getAttribute(Configuration.NAME), optValue);
        }
        return map;
    }

    private Element getInitialElement(String definition) {
        Element testsuite = doc.createElement(Configuration.TESTSUITE);
        String name = getReportFilename().replaceFirst("-report.xml", "");
        name = name.replaceAll("\\.", "/");
        name = name.replaceFirst("/", ".");
        testsuite.setAttribute(Configuration.NAME,
                name.replaceFirst("/", "\\."));
        return testsuite;
    }

    public Element createReportElement(String testcase, String status,
            String time, String output, String error, Task task,
            String expected, boolean failureCondition) {
        Element testcaseE = doc.createElement(Configuration.TESTCASE);
        testcaseE.setAttribute(Configuration.NAME, testcase);
        testcaseE.setAttribute(Configuration.STATUS, status);
        testcaseE.setAttribute(Configuration.TIME, time);

        Element sysout = doc.createElement(Configuration.SYSTEM_OUT);
        sysout.setTextContent(output);

        Element syserr = doc.createElement(Configuration.SYSTEM_ERR);
        syserr.setTextContent(error);

        testcaseE.appendChild(syserr);
        testcaseE.appendChild(sysout);

        if (failureCondition) {
            Element error_ = doc.createElement(Configuration.ERROR);
            error_.setTextContent(task.getStderr());
            error_.setAttribute(Configuration.MESSAGE, task.getStderr());
            testcaseE.appendChild(error_);

            Element failure = doc.createElement("failure");
            failure.setTextContent("Expecting:\n" + expected
                    + "\nbut returned:\n" + task.getStdout());
            testcaseE.appendChild(failure);
        }

        return testcaseE;
    }

    public Task getUnixOnlyScriptTask(File homeDir) {
        if (unixOnlyScript == null)
            return null;
        return new Task(new String[] { unixOnlyScript }, null, homeDir);
    }

    public boolean runOnOS() {
        if (unixOnlyScript != null
                && System.getProperty("os.name").toLowerCase().contains("win")) {
            return false;
        }
        return true;
    }

    public Task getDefinitionTask(File homeDir) {
        ArrayList<String> command = new ArrayList<String>();
        command.add(Configuration.getKompile());
        command.add(language);
        command.add("--directory");
        command.add(getDirectory());
        for (Entry<String, String> entry : kompileOptions.entrySet()) {
            command.add(entry.getKey());
            command.add(entry.getValue());
        }

        String[] arguments = new String[command.size()];
        int i = 0;
        for (String cmd : command) {
            arguments[i] = cmd;
            i++;
        }

        return new Task(arguments, null, homeDir);
    }

    public void deleteFolder(File folder) {
        if (!folder.exists()) {
            return;
        }

        File[] files = folder.listFiles();
        if (files != null) { // some JVMs return null for empty dirs
            for (File f : files) {
                if (f.isDirectory()) {
                    deleteFolder(f);
                } else {
                    f.delete();
                }
            }
        }
        folder.delete();
    }

    public String compileStatus(Task task) {
        return "Compiling " + language + "...\t\t"
                + (compiled(task) ? "success" : "failed");
    }

    public boolean compiled(Task task) {
        if (task.getExit() != 0)
            return false;

        if (!new File(getCompiled()).exists())
            return false;

        if (!task.getStderr().equals(""))
            return false;

        if (!task.getStdout().equals(""))
            return false;

        return true;
    }

    public String getCompiled() {
        return getDirectory() + File.separator + FileUtil.stripExtension(new File(getLanguage()).getName()) + "-kompiled";
    }

    public String getDirectory() {
        return new File(getLanguage()).getAbsoluteFile().getParent();
                //+ (tag.equals("") ? "" : "-" + tag);
    }

    private String getReportFilename() {
        String name = new File(language).getName();

        String absName = new File(language).getAbsolutePath();
        if (absName.startsWith(Configuration.USER_DIR)) {
            name = absName.substring(Configuration.USER_DIR.length() + 1);
        }

        if (!GlobalSettings.isWindowsOS()) {
            name = name.replaceAll(Configuration.FILE_SEPARATOR, ".");

        }
        
        name = name.replaceFirst("\\.k$", "-report.xml");
        if (!tag.equals(""))
            name = tag + "." + name;

        return name;
    }

    public void reportCompilation(Task task) {
        String message = compiled(task) ? "success" : "failed";
        if (!task.getStdout().equals("") || !task.getStderr().equals(""))
            if (message.equals("success"))
                message = "unstable";

        report.appendChild(createReportElement(new File(language).getName(),
                message, task.getElapsed() + "", task.getStdout(),
                task.getStderr(), task, "", !compiled(task)));
        if (Configuration.REPORT) {
            save();
        }
    }

    public void reportPdfCompilation(Task task) {
        String message = compiledPdf(task) ? "success" : "failed";
        if (!task.getStdout().equals(""))
            if (message.equals("success"))
                message = "unstable";

        report.appendChild(createReportElement(new File(getXmlLanguage())
                .getName().replaceFirst("\\.k$", ".pdf"), message,
                task.getElapsed() + "", task.getStdout(), task.getStderr(),
                task, "", !compiledPdf(task)));
        if (Configuration.REPORT)
            save();
    }

    public boolean compiledPdf(Task task) {
        if (task.getExit() != 0)
            return false;

        if (!new File(getPdfCompiledFilename()).exists())
            return false;

        if (!task.getStderr().equals(""))
            return false;

        if (!task.getStdout().equals(""))
            return false;

        return true;
    }

    private String getPdfCompiledFilename() {
        return getDirectory() + File.separator + FileUtil.stripExtension(new File(getLanguage()).getName()) + ".pdf";
    }

    public void save() {
        String reportPath = Configuration.JR + Configuration.FILE_SEPARATOR
                + getReportFilename();
        new File(Configuration.JR).mkdirs();
        try {

            File repFile = new File(reportPath);
            if (!repFile.exists())
                repFile.createNewFile();

            FileWriter fstream = new FileWriter(reportPath);
            BufferedWriter out = new BufferedWriter(fstream);
            out.write(format(doc));
            out.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static String format(Document document) {
        Transformer transformer;
        try {
            transformer = TransformerFactory.newInstance().newTransformer();
            transformer.setOutputProperty(OutputKeys.INDENT, Configuration.YES);

            // initialize StreamResult with File object to save to file
            StreamResult result = new StreamResult(new StringWriter());
            DOMSource source = new DOMSource(document);
            transformer.transform(source, result);
            return result.getWriter().toString();

        } catch (TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (TransformerFactoryConfigurationError e) {
            e.printStackTrace();
        } catch (TransformerException e) {
            e.printStackTrace();
        }
        return null;
    }

    public Task getPdfDefinitionTask(File homeDir) {
        ArrayList<String> command = new ArrayList<String>();
        command.add(Configuration.getKompile());
        command.add(language);
        command.add("--backend");
        command.add("pdf");
        command.add("--directory");
        command.add(getDirectory());
        String[] arguments = new String[command.size()];
        int i = 0;
        for (String cmd : command) {
            arguments[i] = cmd;
            i++;
        }

        return new Task(arguments, null, homeDir);
    }

    private String getXmlLanguage() {
        return getCompiled() + Configuration.FILE_SEPARATOR + "defx.bin";
        // return language;
    }

    public List<Program> getPrograms() {
        return programs;
    }

    public String getLanguage() {
        return language;
    }

    @Override
    public int compareTo(Test o) {
        int d;
        if (o == this)
            return 0;
        d = this.getReportFilename().compareTo(o.getReportFilename());
        if (d != 0)
            return d;
        d = (this.hashCode() == (o.hashCode())) ? 0 : 1;
        return d;
    }

    @Override
    public String toString() {
        return "[" + language + "]" + " ---> " + getReportFilename() + "\n"
                + programs + "\n\n";
    }

    public String getTag() {
        if (!tag.equals(""))
            return "(" + tag + ")";
        return "";
    }


    public boolean isSkipPdf() {
        return skipPdf;
    }

    public boolean isSkipKompile() {
        return skipKompile;
    }

    public boolean isSkipPrograms() {
        return skipPrograms;
    }
}
