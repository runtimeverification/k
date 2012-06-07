import java.io.File;
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
	public static int THREAD_POOL_SIZE = 24;
	public static int ulimit = 120;
	
	public static List<Example> getExamples(String configuration, String k3jar) {
		Document document = getDocument(configuration);

		List<Example> examples = new LinkedList<Example>();

		NodeList exampless = document.getElementsByTagName("example");
		for (int i = 0; i < exampless.getLength(); i++) {
			Element example = (Element) exampless.item(i);
			String dir = toolsDir + fileSep + "Jenkins" + fileSep + kbase
					+ example.getAttribute("dir");
			String mainFile = example.getAttribute("mainfile");
			String mainModule = example.getAttribute("mainmodule");
			String compiledFile = example.getAttribute("compiledfile");

			List<Program> programs = new LinkedList<Program>();
			NodeList tests = example.getElementsByTagName("test");
			for(int j = 0; j < tests.getLength(); j++)
			{
				Element test = (Element) tests.item(j);
				String file = toolsDir + fileSep + "Jenkins" + fileSep + kbase + fileSep + test.getAttribute("file");
				String input = toolsDir + fileSep + "Jenkins" + fileSep + kbase + fileSep + test.getAttribute("input");
				String output = toolsDir + fileSep + "Jenkins" + fileSep + kbase + fileSep + test.getAttribute("output");
				
				programs.add(new Program(file, input, output, "", mainFile, dir));
			}
			
			Example e = new Example(dir, mainFile, mainModule, new String[] {},
					k3jar, compiledFile, programs);
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

}
