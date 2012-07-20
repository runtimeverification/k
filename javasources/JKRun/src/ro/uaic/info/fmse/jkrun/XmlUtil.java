package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class XmlUtil {


	public static StringBuilder colorSymbol(String text, String symbol, String color) {
		StringBuilder aux = new StringBuilder();
		String[] tokens;
		tokens = text.split("\\" + symbol);
		for (int i = 0; i < tokens.length - 1; i++) {
			aux.append(tokens[i]);
			aux.append(color);
			aux.append(symbol);
			aux.append(PrettyPrintOutput.ANSI_NORMAL);
		}
		aux.append(tokens[tokens.length - 1]);
		return aux;
	}

	public static String buildWhitespace(int numChars) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < numChars; i++)
			sb.append(" ");
		return sb.toString();
	}

	// Function to read DOM Tree from File
	public static Document readXML(File f) {

		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		Document doc = null;
		try {
			builder = dbf.newDocumentBuilder();
			InputSource input = new InputSource(new FileInputStream(f));
			doc = builder.parse(input);
		} catch (ParserConfigurationException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (SAXException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (FileNotFoundException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (IOException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		}
		return doc;
	}

	public static ArrayList<Element> getChildElements(Node node) {
		ArrayList l = new ArrayList();
		for (Node childNode = node.getFirstChild(); childNode != null;) {
			if (childNode.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) childNode;
				l.add(elem);
			}
			Node nextChild = childNode.getNextSibling();
			childNode = nextChild;
		}

		return l;
	}

	public static Element getNextSiblingElement(Node node) {
		Node nextSibling = node.getNextSibling();
		while (nextSibling != null) {
			if (nextSibling.getNodeType() == Node.ELEMENT_NODE) {
				return (Element) nextSibling;
			}
			nextSibling = nextSibling.getNextSibling();
		}

		return null;
	}

	public static Element getPreviousSiblingElement(Node node) {
		Node previousSibling = node.getPreviousSibling();
		while (previousSibling != null) {
			if (previousSibling.getNodeType() == Node.ELEMENT_NODE) {
				return (Element) previousSibling;
			}
			previousSibling = previousSibling.getPreviousSibling();
		}

		return null;
	}

	public static String convertNodeToString(Node node) {
		try {
			Transformer t = TransformerFactory.newInstance().newTransformer();
			t.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
			StringWriter sw = new StringWriter();
			t.transform(new DOMSource(node), new StreamResult(sw));
			return sw.toString();
		} catch (TransformerException e) {
			// e.printStackTrace();
			Error.report("Error while convert node to string:"+ e.getMessage());
		}
		return null;
	}

	// write the XML document to disk
	public static void serializeXML(Document doc, String fileName) {
		FileOutputStream f = null;
		try {
			Source xmlSource = new DOMSource(doc);
			f = new FileOutputStream(fileName);
			Result result = new StreamResult(f);
			TransformerFactory transformerFactory = TransformerFactory.newInstance();
			Transformer transformer = transformerFactory.newTransformer();
			// transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
			transformer.setOutputProperty(OutputKeys.INDENT, "yes");
			transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "1");
			transformer.transform(xmlSource, result);
		} catch (TransformerFactoryConfigurationError factoryError) {
			// factoryError.printStackTrace();
			Error.report("Error creating TransformerFactory:" + factoryError.getMessage());
		} catch (TransformerException transformerError) {
			// transformerError.printStackTrace();
			Error.report("Error transforming document:" + transformerError.getMessage());
		} catch (IOException ioException) {
			// ioException.printStackTrace();
			Error.report("Error while serialize XML:" + ioException.getMessage());
		}
		finally{
			if (f != null) {
				try {
					f.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
	}

}