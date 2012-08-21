package k.utils;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class XmlLoader {

	public static Document getXMLDoc(String toParse) {

		try {
			// parse the xml returned by the parser.
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			InputStream is = new ByteArrayInputStream(toParse.getBytes("UTF-8"));
			Document doc = db.parse(is);

			return doc;

		} catch (Exception e) {
			e.printStackTrace();
		}

		return null;
	}

	public static void reportErrors(Document doc) {
		// report any error that xml parser returns
		NodeList nl = doc.getElementsByTagName("error");

		if (nl.getLength() > 0) {
			Node nodeElem = nl.item(0);
			String attr = nodeElem.getAttributes().getNamedItem(Tag.value).getNodeValue();
			NodeList ch = nodeElem.getChildNodes();
			for (int i = 0; i < ch.getLength(); i++) {
				if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
					Element node = (Element) ch.item(i);
					if (node.getNodeName().equals(Tag.localized)) {
						String msg = node.getAttribute("message");
						String file = node.getAttribute("filename");
						String location = node.getAttribute("loc");
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, attr + ": " + msg, file, location, 0));
					}
				}
			}
		}
	}

	public static void reportErrors(Document doc, String fromWhere) {
		// report any error that xml parser returns
		NodeList nl = doc.getElementsByTagName("error");

		if (nl.getLength() > 0) {
			Node nodeElem = nl.item(0);
			String attr = nodeElem.getAttributes().getNamedItem(Tag.value).getNodeValue();
			NodeList ch = nodeElem.getChildNodes();
			for (int i = 0; i < ch.getLength(); i++) {
				if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
					Element node = (Element) ch.item(i);
					if (node.getNodeName().equals(Tag.localized)) {
						String msg = node.getAttribute("message");
						if (msg.equals("Unexpected end of file"))
							msg = "Unexpected end of " + fromWhere;
						String file = node.getAttribute("filename");
						String location = node.getAttribute("loc");
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, attr + ": " + msg, file, location, 0));
					}
				}
			}
		}
	}

	public static Node updateLocation(Node node, int startLine, int startCol) {
		if (Node.ELEMENT_NODE == node.getNodeType()) {
			NamedNodeMap attr = node.getAttributes();
			Node item = attr.getNamedItem(Tag.location);
			if (item != null) {
				String location = item.getNodeValue();
				int loc0 = getLocNumber(location, 0);
				int loc1 = getLocNumber(location, 1);
				int loc2 = getLocNumber(location, 2);
				int loc3 = getLocNumber(location, 3);

				if (loc0 + loc1 + loc2 + loc3 == 0) {
					loc0 = startLine;
					loc1 = startCol;
					loc2 = startLine;
					loc3 = startCol;
				} else {
					if (loc0 == 1)
						loc1 += startCol - 1;
					if (loc2 == 1)
						loc3 += startCol - 1;
					loc0 += startLine - 1;
					loc2 += startLine - 1;
				}

				String newLoc = "(" + loc0 + "," + loc1 + "," + loc2 + "," + loc3 + ")";
				item.setNodeValue(newLoc);
			}
		}
		NodeList list = node.getChildNodes();
		for (int i = 0; i < list.getLength(); i++) {
			// Get child node
			Node childNode = list.item(i);

			// Visit child node
			updateLocation(childNode, startLine, startCol);
		}
		return node;
	}

	public static Node addFilename(Node node, String filename) {
		if (Node.ELEMENT_NODE == node.getNodeType()) {
			NamedNodeMap attr = node.getAttributes();
			Node item = attr.getNamedItem(Tag.location);
			if (item != null) {
				Element e = (Element) node;
				// don't add filename during testing, it takes too much space
				if (!GlobalSettings.noFilename)
					e.setAttribute("filename", filename);
			}
		}
		NodeList list = node.getChildNodes();
		for (int i = 0; i < list.getLength(); i++) {
			// Get child node
			Node childNode = list.item(i);

			// Visit child node
			addFilename(childNode, filename);
		}
		return node;
	}

	public static int getLocNumber(String loc, int place) {
		String[] str = loc.split("[\\(,\\)]");
		return Integer.parseInt(str[place + 1]);
	}

	public static void writeXmlFile(Document doc, String filename) {
		try {
			// Prepare the DOM document for writing
			Source source = new DOMSource(doc);

			// Prepare the output file
			File file = new File(filename);
			Result result = new StreamResult(file);

			// Write the DOM document to the file
			Transformer xformer = TransformerFactory.newInstance().newTransformer();
			xformer.transform(source, result);
		} catch (TransformerConfigurationException e) {
			e.printStackTrace();
		} catch (TransformerException e) {
			e.printStackTrace();
		}
	}
}
