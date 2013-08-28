package org.kframework.main;

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

import org.kframework.execution.Execution;
import org.kframework.execution.Task;
import org.kframework.tests.Program;
import org.kframework.tests.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class Main {

	private static final String HELP_MESSAGE = getHelpMessage();
	private static boolean TEST_MODE = false;

	public static void main(String[] args1) {

		int exitCode = 0;
		File homeDir = new File(System.getProperty("user.dir"));
		boolean error = false;
		String[] args;
		if (args1.length >= 1) {

			// if -test is set then set TEST_MODE and recover the rest of the
			// arguments in args
			if (args1[0].equals("-test")) {
				TEST_MODE = true;
				args = new String[args1.length - 1];
				for (int i = 0; i < args1.length - 1; i++) {
					args[i] = args1[i + 1];
				}
			} else {
				args = new String[args1.length];
				for (int i = 0; i < args1.length; i++) {
					args[i] = args1[i];
				}
			}

			// command line options
			if (args.length > 0) {

				// help
				if (args[0].equals("-h") || args[0].equals("--h")
						|| args[0].equals("-help") || args[0].equals("--help")) {
					System.out.println(HELP_MESSAGE);
					System.exit(0);
				}

				// by default consider args[0] the configuration file
				if (!new File(args[0]).isAbsolute())
					Configuration.CONFIG = Configuration.getHome()
							+ Configuration.FS + args[0];
				else
					Configuration.CONFIG = args[0];

				// report error if configuration file does not exists
				if (!new File(Configuration.getConfig()).exists()) {
					System.out.println("Configuration file "
							+ Configuration.getConfig() + " does not exists.");
					System.exit(1);
				}
			} else {
				error = true;
			}
		}

		if (TEST_MODE && error) {
			System.out.println("Please provide a test configuration file!");
			System.exit(2);
		}

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
