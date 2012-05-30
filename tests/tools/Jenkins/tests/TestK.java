import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import static org.junit.Assert.assertTrue;

public class TestK {
	String kbase = "k-framework";
	File file;
	String toolsDir;
	String fileSep = System.getProperty("file.separator");
	String k3Jar, krun, kompile;
	ThreadPoolExecutor pool;
	int THREAD_POOL_SIZE = 24;

	@Test
	public void buildK() throws InterruptedException, URISyntaxException {

		file = new File(getClass().getProtectionDomain().getCodeSource()
				.getLocation().toURI().getPath());
		toolsDir = file.getAbsolutePath().replaceFirst("/Jenkins.*?$", "");

		// first, checkout K -> verify the existence of k-framework dir.
		Integer ulimit = 120;
		System.out.println("Checkout K ...");
		String[] commands = new String[] { "svn", "checkout",
				"https://k-framework.googlecode.com/svn/trunk", kbase };
		Executor executor = new Executor(commands, ".");
		executor.start();
		executor.join(ulimit * 1000);
		Thread.yield();
		assertTrue(new File(kbase).exists());
		System.out.println("Done.");
		// System.out.println(executor.getOutput());
		// System.out.println(executor.getError());

		// build K -> verify if the k3.jar file was created
		commands = new String[] { "ant" };
		System.out.println("Build ...");
		Executor build = new Executor(commands, toolsDir + fileSep + kbase);
		build.start();
		build.join(ulimit * 1000);
		Thread.yield();
		k3Jar = toolsDir + fileSep + kbase + fileSep + "dist" + fileSep + "bin"
				+ fileSep + "java" + fileSep + "k3.jar";
		krun = toolsDir + fileSep + kbase + fileSep + "dist" + fileSep + "bin"
				+ fileSep + "krun";
		kompile = toolsDir + fileSep + kbase + fileSep + "dist" + fileSep
				+ "bin" + fileSep + "kompile";
		// / System.out.println(k3Jar);
		assertTrue(new File(k3Jar).exists());
		System.out.println("Done.");

		// System.out.println(build.getOutput());
		// System.out.println(build.getError());

		System.out.println("Compiling examples...");
		String configuration = file.getAbsolutePath().replaceFirst(
				"/Jenkins.*?$", "")
				+ fileSep + "configuration.xml";
		List<Example> examples = getExamples(configuration, k3Jar);
		pool = (ThreadPoolExecutor) Executors
				.newFixedThreadPool(THREAD_POOL_SIZE);
		for (Example example : examples)
			pool.execute(example);

		// wait until examples are running
		while (pool.getCompletedTaskCount() != examples.size()) {
			Thread.sleep(1);
		}

		for (Example example : examples) {
			assertTrue(example.isCompiled());
		}
	}

	private List<Example> getExamples(String configuration, String k3jar) {
		Document document = getDocument(configuration);

		List<Example> examples = new LinkedList<Example>();

		NodeList exampless = document.getElementsByTagName("example");
		for (int i = 0; i < exampless.getLength(); i++) {
			Element example = (Element) exampless.item(i);
			String dir = toolsDir + fileSep + kbase
					+ example.getAttribute("dir");
			String mainFile = example.getAttribute("mainfile");
			String mainModule = example.getAttribute("mainmodule");
			String compiledFile = example.getAttribute("compiledfile");

			Example e = new Example(dir, mainFile, mainModule, new String[] {},
					k3jar, compiledFile, null);
			examples.add(e);
		}

		return examples;
	}

	private Document getDocument(String xmlFileName) {
		try {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db;
			db = dbf.newDocumentBuilder();
			Document doc = db.parse(xmlFileName);
			return doc;
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

		return null;
	}
}
