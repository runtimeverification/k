package org.kframework.main;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

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

	public static void main(String[] args) {

		int exitCode = 0;
		File homeDir = new File(System.getProperty("user.dir"));
		System.out.println(homeDir.getAbsolutePath());

		// a little bit hack-ish but it works until somebody complains
		System.out.println(System.getProperty("user.dir"));
		if (System.getProperty("user.dir").contains("jenkins")) {

			// remove anything from previous build
			try {
				ProcessBuilder pb = new ProcessBuilder("rm", "-rf",
						Configuration.k);
				Process process = pb.start();
				int exit = process.waitFor();
				String out = Task.readString(process.getInputStream());
				String err = Task.readString(process.getErrorStream());
				System.out.println(out);
				System.out.println(err);
				System.out.println(exit);
			} catch (Exception e) {
				e.printStackTrace();
				exitCode = 1;
			}

			// remove maude binaries
			/*
			 * System.out.println("Remove maude binaries"); try { ProcessBuilder
			 * pb = new ProcessBuilder("rm", "-rf",
			 * "/var/lib/jenkins/workspace/k-framework/dist/bin/maude/binaries",
			 * Configuration.k); Process process = pb.start(); int exit =
			 * process.waitFor(); String out =
			 * Task.readString(process.getInputStream()); String err =
			 * Task.readString(process.getErrorStream());
			 * System.out.println(out); System.out.println(err);
			 * System.out.println(exit); } catch (Exception e) { exitCode = 1;
			 * e.printStackTrace(); }
			 */
			// first copy the k-framework artifacts
			try {
				ProcessBuilder pb = new ProcessBuilder("cp", "-r",
						"/var/lib/jenkins/workspace/k-framework",
						Configuration.k);
				Process process = pb.start();
				int exit = process.waitFor();
				String out = Task.readString(process.getInputStream());
				String err = Task.readString(process.getErrorStream());
				System.out.println(out);
				System.out.println(err);
				System.out.println(exit);
			} catch (Exception e) {
				exitCode = 1;
				e.printStackTrace();
			}

			// build K
			try {
				ProcessBuilder pb = new ProcessBuilder("ant");
				pb.directory(new File(Configuration.getHome()));
				Process process = pb.start();
				int exit = process.waitFor();
				String out = Task.readString(process.getInputStream());
				String err = Task.readString(process.getErrorStream());
				System.out.println(out);
				System.out.println(err);
				if (exit != 0)
					System.exit(exit);
			} catch (Exception e) {
				exitCode = 1;
				e.printStackTrace();
			}

			if (!new File(Configuration.getHome() + Configuration.FS + "dist"
					+ Configuration.FS + "bin" + Configuration.FS + "java"
					+ Configuration.FS + "k3.jar").exists()) {
			}
			
			homeDir = new File(System.getProperty("user.dir") + Configuration.FS + Configuration.k);
		}

		if (args.length == 1) {
			if (!new File(args[0]).isAbsolute())
				Configuration.CONFIG = Configuration.getHome()
						+ Configuration.FS + args[0];
			else
				Configuration.CONFIG = args[0];
		}
		if (!new File(Configuration.getConfig()).exists()) {
			System.out.println("Configuration file "
					+ Configuration.getConfig() + " does not exists.");
			System.exit(1);
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
		System.out.println("Kompiling the language definitions...");
		Map<Test, Task> definitions = new HashMap<Test, Task>();
		for (Test test : alltests) {
			Task def = test.getDefinitionTask(homeDir);
			definitions.put(test, def);
			Execution.execute(def);
		}
		Execution.finish();

		// report
		for (Entry<Test, Task> entry : definitions.entrySet()) {
			entry.getKey().reportCompilation(entry.getValue());
		}

		// console display
		String kompileStatus = "\n";
		for (Entry<Test, Task> entry : definitions.entrySet()) {
			if (!entry.getKey().compiled(entry.getValue())) {
				kompileStatus += "FAIL: "
						+ entry.getKey().getLanguage()
								.substring(Configuration.getHome().length())
						+ "\n";
				exitCode = 1;
			}
		}
		if (kompileStatus.equals("\n"))
			kompileStatus = "SUCCESS";
		System.out.println(kompileStatus);

		// compile pdf definitions
		System.out.println("Generating PDF documentation...");
		Map<Test, Task> pdfDefinitions = new HashMap<Test, Task>();
		for (Test test : alltests) {
			// also compile pdf if set
			if (test.getPdf()) {
				Task pdfDef = test.getPdfDefinitionTask(homeDir);
				pdfDefinitions.put(test, pdfDef);
				Execution.execute(pdfDef);
			}
		}

		Execution.finish();
		// report
		for (Entry<Test, Task> entry : pdfDefinitions.entrySet()) {
			entry.getKey().reportPdfCompilation(entry.getValue());
		}

		// console display
		String pdfKompileStatus = "\n";
		for (Entry<Test, Task> entry : pdfDefinitions.entrySet()) {
			if (!entry.getKey().compiledPdf(entry.getValue())) {
				pdfKompileStatus += "FAIL: "
						+ entry.getKey().getLanguage()
								.substring(Configuration.getHome().length())
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
			if (test.compiled(dentry.getValue())) {

				System.out.println("Running "
						+ test.getLanguage().substring(
								Configuration.getHome().length())
						+ " programs... ");

				// execute
				List<Program> pgms = test.getPrograms();
				Map<Program, Task> all = new HashMap<Program, Task>();
				for (Program p : pgms) {
					Task task = p.getTask(homeDir);
					all.put(p, task);
					Execution.tpe.execute(task);
				}

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
