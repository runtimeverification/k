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
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

public class Test implements Comparable<Test> {

	private static final String PARSER_HOME = "parser-home";
	private static final String MESSAGE = "message";
	private static final String ERROR2 = "error";
	private static final String SYSTEM_ERR = "system-err";
	private static final String SYSTEM_OUT = "system-out";
	private static final String TIME2 = "time";
	private static final String STATUS2 = "status";
	private static final String TESTCASE2 = "testcase";
	private static final String TESTSUITE2 = "testsuite";
	private static final String KRUN_OPTION = "krun-option";
	private static final String ALL_PROGRAMS = "all-programs";
	private static final String KOMPILE_OPTION = "kompile-option";
	private static final String PROGRAM2 = "program";
	private static final String NAME = "name";
	private static final String EXCLUDE = "exclude";
	private static final String EXTENSIONS2 = "extensions";
	private static final String RECURSIVE2 = "recursive";
	private static final String YES = "yes";
	private static final String PDF2 = "pdf";
	private static final String TITLE = "title";
	private static final String REPORT_DIR = "report-dir";
	private static final String RESULTS = "results";
	private static final String FOLDER = "folder";
	private static final String LANGUAGE2 = "language";
	private static final String IN = ".in";
	private static final String ERR = ".err";
	private static final String OUT = ".out";
	private static final String VALUE = "value";
	private static final String UNIX_ONLY = "unixOnly";

	
	/* data read from config.xml */
	private String language;
	private String programsFolder;
	private String resultsFolder;
	private String tag = "";
    private String unixOnlyScript;
	private boolean recursive;
	private List<String> extensions;
	private List<String> excludePrograms;
	private Map<String, String> kompileOptions = new HashMap<String, String>();
	private Map<String, String> generalKrunOptions = new HashMap<String, String>();
	private List<Program> specialPrograms = new LinkedList<Program>();
	private boolean pdf;
	
	/* data needed for temporary stuff */
	private Document doc;
	public Element report;
	private List<Program> programs;
	private String reportDir = null;

	public Test(Element test) {
		init(test);
		initializePrograms();
	}

	private void initializePrograms() {
		programs = new LinkedList<Program>();

		String[] pgmsFolders = this.programsFolder.split("\\s+");

		if (resultsFolder != null && !new File(getResultsFolder()).exists())
			System.out.println("Folder: " + Configuration.getHome()
					+ Configuration.FS + resultsFolder + " does not exists.");

		for (int i = 0; i < pgmsFolders.length; i++) {
			String programsFolder = pgmsFolders[i];

			if (!new File(Configuration.getHome() + Configuration.FS
					+ programsFolder).exists())
				System.out.println("Folder: " + Configuration.getHome()
						+ Configuration.FS + programsFolder
						+ " does not exists.");

			if (programsFolder == null || programsFolder.equals(""))
				return;

			List<String> allProgramPaths = searchAll(Configuration.getHome()
					+ Configuration.FS + programsFolder, extensions, recursive);

			for (String programPath : allProgramPaths) {
				// ignore the programs from exclude list
				boolean excluded = false;
				for (String exclude : excludePrograms)
					if (programPath.equals(Configuration.getHome()
							+ Configuration.FS + programsFolder
							+ Configuration.FS + exclude))
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
				if (resultsFolder != null) {

					String inputFile = searchInputFile(getResultsFolder(),
							new File(programPath).getName(), recursive);
					input = getFileAsStringOrNull(inputFile);

					String outputFile = searchOutputFile(getResultsFolder(),
							new File(programPath).getName(), recursive);
					output = getFileAsStringOrNull(outputFile);

					String errorFile = searchErrorFile(getResultsFolder(),
							new File(programPath).getName(), recursive);
					error = getFileAsStringOrNull(errorFile);

				}

				// custom programPath
				programPath = programPath.replaceFirst(Configuration.getHome()
						+ Configuration.FS, "");

				Program p = new Program(programPath, krunOptions, this, input,
						output, error);
				programs.add(p);

			}
		}
	}

	private String getResultsFolder() {
		return Configuration.getHome() + Configuration.FS + resultsFolder;
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
		return searchFile(resultsFolder2, name + OUT, recursive);
	}

	private String searchErrorFile(String resultsFolder2, String name,
			boolean recursive2) {
		return searchFile(resultsFolder2, name + ERR, recursive);
	}

	private String searchInputFile(String resultsFolder2, String name,
			boolean recursive) {
		return searchFile(resultsFolder2, name + IN, recursive);
	}

	private String searchFile(String folder, String filename, boolean recursive) {
		String[] files = new File(folder).list();
		String file = null;
		if (files != null)
			for (int i = 0; i < files.length; i++) {
				if (new File(folder + Configuration.FS + files[i]).isFile())
					if (files[i].equals(filename))
						file = new File(folder + Configuration.FS + files[i])
								.getAbsolutePath();
				if (recursive)
					if (new File(folder + Configuration.FS + files[i])
							.isDirectory())
						file = searchFile(folder + Configuration.FS + files[i],
								filename, recursive);

				if (file != null)
					return file;
			}

		return file;
	}

	private List<String> searchAll(String programsFolder,
			List<String> extensions, boolean recursive) {

		List<String> paths = new LinkedList<String>();
		for (String extension : extensions)
			paths.addAll(searchAll(programsFolder, extension));

		if (recursive) {
			String[] files = new File(programsFolder).list();
			if (files != null)
				for (int i = 0; i < files.length; i++) {
					if (new File(programsFolder + Configuration.FS + files[i])
							.isDirectory()) {
						paths.addAll(searchAll(programsFolder
								+ Configuration.FS + files[i], extensions,
								recursive));
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
				if (new File(programsFolder2 + Configuration.FS + files[i])
						.isFile()) {
					if (files[i].endsWith(extension))
						fls.add(programsFolder2 + Configuration.FS + files[i]);
				}
		}
		return fls;
	}

	private void init(Element test) {
		String homeDir = Configuration.getHome();

		// get full name
		language = test.getAttribute(LANGUAGE2);

		// get programs dir
		programsFolder = test.getAttribute(FOLDER);

		// get tests results
		resultsFolder = test.getAttribute(RESULTS);
		if (resultsFolder.equals(""))
			resultsFolder = null;

		// get tests results
		reportDir = test.getAttribute(REPORT_DIR);
		if (reportDir.equals(""))
			reportDir = null;

        unixOnlyScript = test.getAttribute(UNIX_ONLY);
        if (unixOnlyScript.equals(""))
            unixOnlyScript = null;

		// get Jenkins tag
		tag = test.getAttribute(TITLE);

		// get pdf
		if (test.getAttribute(PDF2).equals(YES)
				|| test.getAttribute(PDF2).equals(""))
			pdf = true;
		else
			pdf = false;

		// set recursive
		String rec = test.getAttribute(RECURSIVE2);
		if (rec.equals("") || rec.equals(YES))
			recursive = true;
		else
			recursive = false;

		// extensions
		extensions = Arrays
				.asList(test.getAttribute(EXTENSIONS2).split("\\s+"));

		// exclude programs
		excludePrograms = Arrays.asList(test.getAttribute(EXCLUDE)
				.split("\\s+"));

		// kompile options
		NodeList kompileOpts = test.getElementsByTagName(KOMPILE_OPTION);
		for (int i = 0; i < kompileOpts.getLength(); i++) {
			Element option = (Element) kompileOpts.item(i);
			kompileOptions.put(option.getAttribute(NAME),
					option.getAttribute(VALUE));
		}

		// load programs with special option
		NodeList specialPgms = test.getElementsByTagName(PROGRAM2);
		for (int i = 0; i < specialPgms.getLength(); i++) {
			Element pgm = (Element) specialPgms.item(i);
			String programPath = pgm.getAttribute(NAME);

			Map<String, String> map = getKrunOptions(pgm);

			String input = null;
			String output = null;
			String error = null;
			if (resultsFolder != null) {

				String inputFile = searchInputFile(getResultsFolder(),
						new File(programPath).getName(), recursive);
				input = getFileAsStringOrNull(inputFile);

				String outputFile = searchOutputFile(getResultsFolder(),
						new File(programPath).getName(), recursive);
				output = getFileAsStringOrNull(outputFile);

				String errorFile = searchErrorFile(getResultsFolder(),
						new File(programPath).getName(), recursive);
				error = getFileAsStringOrNull(errorFile);

			}

			Program program = new Program(homeDir + Configuration.FS
					+ programPath, map, this, input, output, error);
			specialPrograms.add(program);
		}

		// general krun options
		NodeList genOpts = test.getElementsByTagName(ALL_PROGRAMS);
		if (genOpts != null && genOpts.getLength() > 0) {
			Element all = (Element) genOpts.item(0);
			generalKrunOptions = getKrunOptions(all);
		}

		if (genOpts.getLength() == 0) {
			generalKrunOptions.put("--no-color", "");
			generalKrunOptions.put("--output-mode", "none");
		}

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
	}

	private Map<String, String> getKrunOptions(Element parent) {
		Map<String, String> map = new HashMap<String, String>();
		NodeList opts = parent.getElementsByTagName(KRUN_OPTION);
		for (int j = 0; j < opts.getLength(); j++) {
			Element krunOpt = (Element) opts.item(j);

			// unescape < and >
			String optValue = krunOpt.getAttribute(VALUE);
			optValue = optValue.replaceAll("&lt;", "<");
			optValue = optValue.replaceAll("&gt;", ">");

			String parserHome = krunOpt.getAttribute(PARSER_HOME);
			String parser = System.getenv(parserHome);
			if (parser != null) {
				optValue = parser + System.getProperty("file.separator") + optValue;
			}
			
			map.put(krunOpt.getAttribute(NAME), optValue);
		}
		return map;
	}

	private Element getInitialElement(String definition) {
		Element testsuite = doc.createElement(TESTSUITE2);
		String name = "";
		if (reportDir != null)
			name = reportDir;
		else
			name = new File(language).getParent();

		if (!tag.equals(""))
			name = tag + "/" + name;

		testsuite.setAttribute(NAME, name.replaceFirst("/", "\\."));
		return testsuite;
	}

	public Element createReportElement(String testcase, String status,
			String time, String output, String error, Task task,
			String expected, boolean failureCondition) {
		Element testcaseE = doc.createElement(TESTCASE2);
		testcaseE.setAttribute(NAME, testcase);
		testcaseE.setAttribute(STATUS2, status);
		testcaseE.setAttribute(TIME2, time);

		Element sysout = doc.createElement(SYSTEM_OUT);
		sysout.setTextContent(output);

		Element syserr = doc.createElement(SYSTEM_ERR);
		syserr.setTextContent(error);

		testcaseE.appendChild(syserr);
		testcaseE.appendChild(sysout);

		if (failureCondition) {
			Element error_ = doc.createElement(ERROR2);
			error_.setTextContent(task.getStderr());
			error_.setAttribute(MESSAGE, task.getStderr());
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
        return new Task(new String[] {unixOnlyScript}, null, homeDir);
    }

    public boolean runOnOS() {
        if (unixOnlyScript != null && System.getProperty("os.name").toLowerCase().contains("win")) {
            return false;
        }
        return true;
    }

	public Task getDefinitionTask(File homeDir) {
		ArrayList<String> command = new ArrayList<String>();
		command.add(Configuration.getKompile());
		command.add(language);
		command.add("-o");
		command.add(getCompiled());
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

		
		/* Before running the definition, delete the temporary files if they exists */
		deleteFolder(new File(getCompiled()));
		
		return new Task(arguments, null, homeDir);
	}

	public void deleteFolder(File folder) {
		if (!folder.exists()) {
			return;
		}
		
	    File[] files = folder.listFiles();
	    if(files!=null) { //some JVMs return null for empty dirs
	        for(File f: files) {
	            if(f.isDirectory()) {
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
		return getLanguage().replaceAll("\\.k$", "") + "-kompiled" + (tag.equals("") ? "" : "-" + tag);
	}

	private String getReportFilename() {
		String name = language.replaceFirst("\\.k$", "-report.xml").replaceAll(
				"\\/", ".");
		if (reportDir != null)
			name = reportDir + "-report.xml";

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

		save();
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
		return getLanguage().replaceAll("\\.k$", ".pdf");

	}

	public void save() {
		String reportPath = Configuration.JR + Configuration.FS
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
			transformer.setOutputProperty(OutputKeys.INDENT, YES);

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

	public boolean getPdf() {
		return pdf;
	}

	public Task getPdfDefinitionTask(File homeDir) {
		ArrayList<String> command = new ArrayList<String>();
		command.add(Configuration.getKompile());
		command.add(language);
		command.add("--pdf");
		command.add("-o");
		command.add(getPdfCompiledFilename());
		String[] arguments = new String[command.size()];
		int i = 0;
		for (String cmd : command) {
			arguments[i] = cmd;
			i++;
		}

		return new Task(arguments, null, homeDir);
	}

	private String getXmlLanguage() {
		return getCompiled() + Configuration.FS + "defx.bin";
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
		d = this.programsFolder.compareTo(o.programsFolder);
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
}
