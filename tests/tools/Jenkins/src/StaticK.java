import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ThreadPoolExecutor;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class StaticK {
	public static String kbase = "k-framework";
	public static File file;
	public static String toolsDir;
	public static String fileSep = System.getProperty("file.separator");
	public static String k3Jar, JKrun;
	public static ThreadPoolExecutor pool;
	public static int THREAD_POOL_SIZE = 18;
	public static int ulimit = 120;
	public static Report report = new Report("junit-report.xml");
	public static String kbasedir;
	public static String configuration;
	
	public static List<Example> getExamples(String configuration, String k3jar, String tagName, String kbasedir) {
		Document document = getDocument(configuration);

		List<Example> examples = new LinkedList<Example>();

		NodeList exampless = document.getElementsByTagName(tagName);
		for (int i = 0; i < exampless.getLength(); i++) {
			Element example = (Element) exampless.item(i);
			String dir = kbasedir
					+ example.getAttribute("dir");
			String mainFile = example.getAttribute("mainfile");
			String mainModule = example.getAttribute("mainmodule");
			String compiledFile = example.getAttribute("compiledfile");

			List<Program> programs = new LinkedList<Program>();
			NodeList tests = example.getElementsByTagName("test");
			for (int j = 0; j < tests.getLength(); j++) {
				Element test = (Element) tests.item(j);
				String file = kbasedir
						+ test.getAttribute("file");
				String input = kbasedir
						+ test.getAttribute("input");
				String output = kbasedir + test.getAttribute("output");

				NodeList options = test.getElementsByTagName("option");
				List<String> krunOptions = new LinkedList<String>();
				for(int k = 0; k < options.getLength(); k++)
				{
					Element option = (Element)options.item(k);
					String name = option.getAttribute("name");
					String value = option.getAttribute("value");
					if (!name.equals(""))
						krunOptions.add(name);
					if (!value.equals(""))
						krunOptions.add(value);
				}
				
				programs.add(new Program(file, input, output, "", mainFile, dir, krunOptions, tagName));
			}

			Example e = new Example(dir, mainFile, mainModule, new String[] {},
					k3jar, compiledFile, programs, tagName);
			examples.add(e);
		}

		return examples;
	}

	private static Document getDocument(String xmlFileName) {
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

	public static String readFileAsString(String filePath) {
		if (new File(filePath).isDirectory())
			return "";
		
		byte[] buffer = new byte[(int) new File(filePath).length()];
		BufferedInputStream f = null;
		try {
			f = new BufferedInputStream(new FileInputStream(filePath));
			f.read(buffer);
		} catch (Exception e) {
			System.out.println(e.getLocalizedMessage());
		} finally {
			if (f != null)
				try {
					f.close();
				} catch (IOException ignored) {
				}
		}
		return new String(buffer);
	}
}
