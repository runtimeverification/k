import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.Map;

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

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.SAXException;

public class Report {

	String file;
	Document doc;
	Element testsuites;
	Map<String, Element> tests;

	public Report(String file) {
		try {
			this.file = file;
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db;
			db = dbf.newDocumentBuilder();
			this.doc = db.newDocument();
		} catch (ParserConfigurationException e) {
			System.out.println(e.getMessage());
			System.exit(1);
		}
		
		tests = new HashMap<String, Element>();
		init();
	}

	public void init() {
		// root of the document
		testsuites = doc.createElement("testsuites");
		doc.appendChild(testsuites);
		testsuites.setAttribute("name", "k-framework");
	}

	public void report(Example example, String suite) {
		Element testsuite = tests.get(suite);
		if (testsuite == null) {
			testsuite = doc.createElement("testsuite");
			testsuite.setAttribute("name", suite);
			tests.put(suite, testsuite);
			testsuites.appendChild(testsuite);
		}

		// create test case
		Element testcase = doc.createElement("testcase");

		// set test case name
		testcase.setAttribute("name", example.getFile());

		// set status
		testcase.setAttribute("status", example.isCompiled() ? "success"
				: "fail");

		// set time
		testcase.setAttribute("time", Long.toString(example.getTime() / 1000));

		// set output
		Element output = doc.createElement("system-out");
		output.setTextContent(example.output);
		testcase.appendChild(output);
		
		// set error
		Element error = doc.createElement("system-err");
		error.setTextContent(example.error);
		testcase.appendChild(error);

		// append testcase to suite
		testsuite.appendChild(testcase);
	}

	
	public void report(Program program, String suite) {
		Element testsuite = tests.get(suite);
		if (testsuite == null) {
			testsuite = doc.createElement("testsuite");
			testsuite.setAttribute("name", suite);
			tests.put(suite, testsuite);
			testsuites.appendChild(testsuite);
		}

		// create test case
		Element testcase = doc.createElement("testcase");

		// set test case name
		testcase.setAttribute("name", program.filename);

		// set status
		testcase.setAttribute("status", program.isCorrect() ? "success"
				: "fail");

		// set time
		testcase.setAttribute("time", Long.toString(program.getTime() / 1000));

		// set output
		Element output = doc.createElement("system-out");
		output.setTextContent(program.getOutput());
		testcase.appendChild(output);
		
		// set error
		Element error = doc.createElement("system-err");
		error.setTextContent(program.getError());
		testcase.appendChild(error);

		// append testcase to suite
		testsuite.appendChild(testcase);
	}

	
	/**
	 * Given an XML file as input it return the DOM Document
	 * 
	 * @param xmlFilePath
	 * @return DOM Document of the file
	 */
	public static Document getDocument(String file) {
		try {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db;
			db = dbf.newDocumentBuilder();
			Document doc = db.parse(file);
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

	public static String format(Document document) {
		Transformer transformer;
		try {
			transformer = TransformerFactory.newInstance().newTransformer();
			transformer.setOutputProperty(OutputKeys.INDENT, "yes");

			// initialize StreamResult with File object to save to file
			StreamResult result = new StreamResult(new StringWriter());
			DOMSource source = new DOMSource(document);
			transformer.transform(source, result);
			return result.getWriter().toString();

		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TransformerFactoryConfigurationError e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	public void save() {
		try {
			FileWriter fstream = new FileWriter(file);
			BufferedWriter out = new BufferedWriter(fstream);
			out.write(format(doc));
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
