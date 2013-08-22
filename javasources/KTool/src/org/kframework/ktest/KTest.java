package org.kframework.ktest;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.apache.commons.cli.CommandLine;
import org.kframework.ktest.execution.Execution;
import org.kframework.ktest.execution.Task;
import org.kframework.ktest.tests.Program;
import org.kframework.ktest.tests.Test;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class KTest {

	public static void test(String[] args) {

		KTestOptionsParser op = new KTestOptionsParser();
		CommandLine cmd = op.parse(args);

		// Help
		if (cmd.hasOption(Configuration.HELP_OPTION))
			KTestOptionsParser.helpExit(op.getHelp(),
					Configuration.HELP_OPTION, op.getOptions());

		// Version
		if (cmd.hasOption(Configuration.VERSION_OPTION)) {
			String msg = FileUtil.getFileContent(KPaths.getKBase(false)
					+ KPaths.VERSION_FILE);
			System.out.println(msg);
			System.exit(0);
		}

		// The language to be tested
		if (cmd.hasOption(Configuration.LANGUAGE_OPTION)) {
			Configuration.KDEF = cmd
					.getOptionValue(Configuration.LANGUAGE_OPTION);
		}

		// Programs folder
		if (cmd.hasOption(Configuration.PROGRAMS_OPTION)) {
			Configuration.PGM_DIR = cmd
					.getOptionValue(Configuration.PROGRAMS_OPTION);
		}

		// List of excluded programs
		if (cmd.hasOption(Configuration.EXCLUDE_OPTION)) {
			Configuration.EXCLUDE_PROGRAMS = Arrays.asList(cmd.getOptionValue(
					Configuration.EXCLUDE_OPTION).split("\\s+"));
		}

		// List of program (non-empty) extensions
		if (cmd.hasOption(Configuration.EXTENSIONS_OPTION)) {
			Configuration.EXTENSIONS = Arrays.asList(cmd.getOptionValue(
					Configuration.EXTENSIONS_OPTION).split("\\s+"));
		}

		// List of program (non-empty) extensions
		if (cmd.hasOption(Configuration.RESULTS_OPTION)) {
			Configuration.RESULTS_FOLDER = cmd
					.getOptionValue(Configuration.RESULTS_OPTION);
		}

		// Resolve the configuration file
		if (cmd.hasOption(Configuration.CONFIG_OPTION)) {
			Configuration.CONFIG = cmd
					.getOptionValue(Configuration.CONFIG_OPTION);
		} 


		// sanity check
		if (Configuration.CONFIG != null
				&& new File(Configuration.KDEF).isFile()) {
			GlobalSettings.kem
					.register(new KException(
							ExceptionType.ERROR,
							KExceptionGroup.CRITICAL,
							"Please provide a root directory for the configuration file.",
							"command line", "System file."));
		}
		if (new File(Configuration.KDEF).isDirectory() && Configuration.CONFIG == null) {
			GlobalSettings.kem
			.register(new KException(
					ExceptionType.ERROR,
					KExceptionGroup.CRITICAL,
					"Please provide a test configuration file.",
					"command line", "System file."));
		}

		// if a configuration file is not given then ktest will run only
		// with command line arguments
		if (Configuration.CONFIG == null) {
			Configuration.SINGLE_DEF_MODE = true;
		}

		// execution
		if (Configuration.SINGLE_DEF_MODE) {
			List<Test> alltests = new LinkedList<Test>();
			
			List<String> pgmsFolder = Configuration.PGM_DIR == null ? new LinkedList<String>() : Arrays.asList(Configuration.PGM_DIR.split("\\s+"));
			List<String> resultsFolder = Configuration.RESULTS_FOLDER == null ? new LinkedList<String>() : Arrays.asList(Configuration.RESULTS_FOLDER.split("\\s+"));
			Test test = new Test(Configuration.KDEF, pgmsFolder, resultsFolder, Configuration.EXTENSIONS, Configuration.EXCLUDE_PROGRAMS, System.getProperty("user.dir"));
			alltests.add(test);
			
			testing(0, new File(System.getProperty("user.dir")), alltests);
		} else {
			testConfig(Configuration.CONFIG, Configuration.KDEF,
					Configuration.PGM_DIR, Configuration.RESULTS_FOLDER);
		}
	}

	/**
	 * Search the absolute path of a given file or throws an error.
	 * 
	 * @param path
	 * @return the absolute path of a file
	 */
//	private static String resolveFullPath(String path) {
//		
//		if (new File(path).isAbsolute()){
//			return new File(path).getAbsolutePath();
//		}
//		
//		if (new File(path).exists())
//			return new File(path).getAbsolutePath();
//		else
//			GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
//					KExceptionGroup.CRITICAL, "Unable to find " + path,
//					"command line", "System file."));
//
//		// this will never happen
//		return null;
//	}

	private static List<Test> parseXMLConfig(String configFile,
			String rootDefDir, String rootProgramsDir, String rootResultsDir)
			throws ParserConfigurationException, SAXException, IOException {
		List<Test> alltests = new LinkedList<Test>();
		DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
		
		if (!new File(configFile).exists()) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
			KExceptionGroup.CRITICAL, "Unable to find " + configFile,
			"command line", "System file."));			
		}
		
		System.out.println("Buildfile: " + configFile);
		Document doc = dBuilder.parse(new File(configFile));
		Element root = doc.getDocumentElement();

		NodeList test = root.getElementsByTagName(Configuration.TEST);
		for (int i = 0; i < test.getLength(); i++)
			alltests.add(new Test((Element) test.item(i), rootDefDir,
					rootProgramsDir, rootResultsDir, System.getProperty("user.dir")));

		return alltests;
	}

	public static void testConfig(String configFile, String rootDir,
			String rootProgramsDir, String rootResultsDir) {

		int exitCode = 0;
		List<Test> alltests = new LinkedList<Test>();

		// load config
		try {
			alltests = parseXMLConfig(configFile, rootDir, rootProgramsDir,
					rootResultsDir);
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			exitCode = 1;
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			exitCode = 1;
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			exitCode = 1;
			e.printStackTrace();
		}

		testing(exitCode, new File(System.getProperty("user.dir")), alltests);
	}

	private static void testing(int exitCode, File homeDir, List<Test> alltests) {
		// compile definitions first
		int i = 0;
		System.out.print("Kompiling the language definitions...");
		Map<Test, Task> definitions = new TreeMap<Test, Task>();
		for (Test test : alltests) {
			Task def = test.getDefinitionTask(homeDir);
			definitions.put(test, def);
			Execution.execute(def);

			if (test.runOnOS()) {
				Task unixOnlyScript = test.getUnixOnlyScriptTask(homeDir);
				if (unixOnlyScript != null) {
					Execution.execute(unixOnlyScript);
				}
			}
			i++;
		}
		System.out.println("(" + i + ")");
		Execution.finish();

		// report
		for (Entry<Test, Task> entry : definitions.entrySet()) {
			entry.getKey().reportCompilation(entry.getValue());
		}

		// console display
		String kompileStatus = "\n";
		for (Entry<Test, Task> entry : definitions.entrySet()) {
			if (!entry.getKey().compiled(entry.getValue())) {
				kompileStatus += "FAIL: " + entry.getKey().getLanguage() + "\n";
				exitCode = 1;
			}
		}
		if (kompileStatus.equals("\n"))
			kompileStatus = "SUCCESS";
		System.out.println(kompileStatus);

		// compile pdf definitions
		i = 0;
		System.out.print("Generating PDF documentation...");
		Map<Test, Task> pdfDefinitions = new TreeMap<Test, Task>();
		for (Test test : alltests) {
			// also compile pdf if set
			if (test.getPdf()) {
				Task pdfDef = test.getPdfDefinitionTask(homeDir);
				pdfDefinitions.put(test, pdfDef);
				Execution.execute(pdfDef);
				i++;
			}
		}
		System.out.println("(" + i + ")");
		Execution.finish();
		// create XML report
		for (Entry<Test, Task> entry : pdfDefinitions.entrySet()) {
			entry.getKey().reportPdfCompilation(entry.getValue());
		}

		// console messages
		String pdfKompileStatus = "\n";
		for (Entry<Test, Task> entry : pdfDefinitions.entrySet()) {
			if (!entry.getKey().compiledPdf(entry.getValue())) {
				pdfKompileStatus += "FAIL: " + entry.getKey().getLanguage()

				+ "\n";
				exitCode = 1;
			}
		}
		if (pdfKompileStatus.equals("\n"))
			pdfKompileStatus = "SUCCESS";
		System.out.println(pdfKompileStatus);

		// execute all programs (for which corresponding definitions are
		// compiled)
		for (Entry<Test, Task> dentry : definitions.entrySet()) {
			Test test = dentry.getKey();
			if (test.compiled(dentry.getValue()) && test.runOnOS()) {

				System.out.print("Running " + test.getLanguage()
						+ " programs... " + test.getTag());

				// execute
				List<Program> pgms = test.getPrograms();
				Map<Program, Task> all = new TreeMap<Program, Task>();
				i = 0;
				for (Program p : pgms) {
					Task task = p.getTask(homeDir);
					all.put(p, task);
					Execution.tpe.execute(task);
					i++;
				}
				System.out.println("(" + i + ")");
				Execution.finish();

				// report
				for (Entry<Program, Task> entry : all.entrySet()) {
					entry.getKey().reportTest(entry.getValue());
				}

				// console
				String pgmOut = "";
				for (Entry<Program, Task> entry : all.entrySet()) {
					if (!entry.getKey().success(entry.getValue())) {
						pgmOut += "FAIL: " + entry.getKey().getProgramPath()
								+ "\n";
						exitCode = 1;
					}
				}
				if (pgmOut.equals(""))
					pgmOut = "SUCCESS";
				System.out.println(pgmOut);
			}
		}

		System.exit(exitCode);
	}

	public static void copyFolder(File src, File dest) throws IOException {

		if (src.getName().startsWith("."))
			return;

		if (src.isDirectory()) {

			// if directory not exists, create it
			if (!dest.exists()) {
				dest.mkdir();
			}

			// list all the directory contents
			String files[] = src.list();

			for (String file : files) {
				// construct the src and dest file structure
				File srcFile = new File(src, file);
				File destFile = new File(dest, file);
				// recursive copy
				copyFolder(srcFile, destFile);
			}

		} else {
			// if file, then copy it
			// Use bytes stream to support all file types
			InputStream in = new FileInputStream(src);
			OutputStream out = new FileOutputStream(dest);

			byte[] buffer = new byte[1024];

			int length;
			// copy the file content in bytes
			while ((length = in.read(buffer)) > 0) {
				out.write(buffer, 0, length);
			}

			in.close();
			out.close();
		}
	}
}
