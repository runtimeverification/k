package org.kframework.ktest;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
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

	private static final String HELP_MESSAGE = getHelpMessage();

	public static void test(String[] args) {
		
		KTestOptionsParser op = new KTestOptionsParser();
		CommandLine cmd = op.parse(args);

		// options: help
		if (cmd.hasOption("help"))
			KTestOptionsParser.helpExit(op.getHelp(), "help", op.getOptions());

		// version
		if (cmd.hasOption("version")) {
			String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
			System.out.println(msg);
			System.exit(0);
		}

		// configuration file
		if (cmd.hasOption("config")) {
			System.out.println("Yes!");
			Configuration.CONFIG = Configuration.getHome()
					+ Configuration.FS + cmd.getOptionValue("config");
		} else {
			System.out.println("Not!");
			// if not given, config is considered to be the default
			String[] restArgs = cmd.getArgs();
			if (restArgs.length < 1)
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Please provide a configuration file", "command line", "System file."));
			else
				Configuration.CONFIG = Configuration.getHome()
						+ Configuration.FS + restArgs[0];

		}
		
		System.out.println(Configuration.CONFIG);
		
		// check existence of the configuration file
		if (!new File(Configuration.CONFIG).exists()) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "The configuration file you provided does not exists", "command line", "System file."));
		}
		
		ktest();
	}
	
	public static void ktest() {

		int exitCode = 0;
		File homeDir = new File(System.getProperty("user.dir"));

		List<Test> alltests = new LinkedList<Test>();

		// load config
		try {
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			System.out.println("Buildfile: " + Configuration.getConfig());
			Document doc = dBuilder.parse(new File(Configuration.getConfig()));
			Element root = doc.getDocumentElement();

			NodeList test = root.getElementsByTagName("test");
			for (int i = 0; i < test.getLength(); i++)
				alltests.add(new Test((Element) test.item(i)));

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

	private static String getHelpMessage() {
		return "usage: [-help] <config.xml>";
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
