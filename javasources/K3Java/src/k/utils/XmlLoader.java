package k.utils;

import java.io.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.*;

public class XmlLoader {

	public static Document createModules(String toParse, String filename) {

		try {
			// parse the xml returned by the parser.
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			InputStream is = new ByteArrayInputStream(toParse.getBytes("UTF-8"));
			Document doc = db.parse(is);

			// report any error that xml parser returns
			if (doc.getDocumentElement().getNodeName().equals(Tag.error)) {
				String attr = doc.getDocumentElement().getAttribute(Tag.value);
				NodeList ch = doc.getDocumentElement().getChildNodes();
				for (int i = 0; i < ch.getLength(); i++) {
					if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
						Element node = (Element) ch.item(i);
						if (node.getNodeName().equals(Tag.localized)) {
							String msg = node.getAttribute("message");
							String file = node.getAttribute("file");
							String location = node.getAttribute("area");
							Error.externalReport(attr + ":" + msg + " at " + file + " location=" + location);
						}
					}
				}
			}

			return doc;

		} catch (Exception e) {
			e.printStackTrace();
		}

		return null;
	}

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

	public static void reportErrors(Node nodeElem) {
		// report any error that xml parser returns
		if (nodeElem.getNodeName().equals(Tag.error)) {
			String attr = nodeElem.getAttributes().getNamedItem(Tag.value).getNodeValue();
			NodeList ch = nodeElem.getChildNodes();
			for (int i = 0; i < ch.getLength(); i++) {
				if (ch.item(i).getNodeType() == Node.ELEMENT_NODE) {
					Element node = (Element) ch.item(i);
					if (node.getNodeName().equals(Tag.localized)) {
						String msg = node.getAttribute("message");
						String file = node.getAttribute("filename");
						String location = node.getAttribute("loc");
						Error.externalReport(attr + ": " + msg + "\n\t at: " + location + " in file: " + file);
					}
				}
			}
		}

	}

	public static Node updateLocation(Node node, int startLine, int startCol, String filename) {
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

				Element e = (Element) node;
				// TODO: don't add filename during testing, it takes too much space
				 e.setAttribute("filename", filename);
			}
		}
		NodeList list = node.getChildNodes();
		for (int i = 0; i < list.getLength(); i++) {
			// Get child node
			Node childNode = list.item(i);

			// Visit child node
			updateLocation(childNode, startLine, startCol, filename);
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
