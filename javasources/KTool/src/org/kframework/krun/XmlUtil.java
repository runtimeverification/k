package org.kframework.krun;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;
import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class XmlUtil {

	// FUNCTION to read DOM Tree from File
	public static Document readXML(File f) {
		try {
			return readXML(new InputSource(new FileInputStream(f)));
		} catch (FileNotFoundException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		}
		return null; //unreachable
	}

	public static Document readXML(String s) {
		return readXML(new InputSource(new StringReader(s)));
	}

	public static Document readXML(InputSource input) {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		Document doc = null;
		try {
			builder = dbf.newDocumentBuilder();
			doc = builder.parse(input);
		} catch (ParserConfigurationException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (SAXException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		} catch (IOException e) {
			// e.printStackTrace();
			Error.report("Error while reading XML:" + e.getMessage());
		}
		return doc;
	}

	public static ArrayList<Element> getChildElements(Node node) {
		ArrayList<Element> l = new ArrayList<Element>();
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

	//convert a node to its string representation
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
	public static void serializeXML(Node doc, String fileName) {
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
	
	//convert the xml obtained from Maude with the -xml-log option back into its Maude representation
	public static String xmlToMaude (String fileName) {
		File input = new File(fileName);
		Document doc = XmlUtil.readXML(input);
		NodeList list = null;
		Node nod = null;
		
		if (K.maude_cmd.equals("erewrite")) {
			list = doc.getElementsByTagName("result");
			nod = list.item(0);
			if (nod == null) {
				Error.report("XmltoMaude: The node with result tag wasn't found");
			} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) nod;
				NodeList child = elem.getChildNodes();
				for (int i = 0; i < child.getLength(); i++) {
					if (child.item(i).getNodeType() == Node.ELEMENT_NODE) {
						return process((Element) child.item(i));
					}
				}
			}
		}
		return "";
		
	}
	
	public static String process(Element node) {
		StringBuilder sb = new StringBuilder();
		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");
		ArrayList<Element> list = XmlUtil.getChildElements(node);
		
		if (sort.equals("#NzNat") && op.equals("sNat_")) {
			sb = new StringBuilder();
			sb.append(node.getAttribute("number"));
			return sb.toString();
		}
		else {
			//n = nr of child nodes
			int n = list.size();
			if (n == 0) {
				sb = new StringBuilder();
				sb.append("(");
				sb.append(op);
				sb.append(")." + sort);
				
				return sb.toString();
			}
			//the node has more than 1 child
			else {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
		   		    Element child = list.get(i);
		   		    String elem = process(child);
					elements.add(elem);
			    }
				sb = new StringBuilder(op);
				sb.append("(");
				for (int i = 0; i < elements.size(); i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
		                sb.append(", ");
					}
				}
				sb.append(")");
				return sb.toString();
			}
			
		}
		
	}
	
	public static Element getTerm(Document doc, String tagName, String attributeName, String xpathExpression, String solutionIdentifier) {
		Element result = null;
		NodeList list = null;
		Node nod = null;
		
		list = doc.getElementsByTagName(tagName);
		if (list.getLength() == 0) {
			Error.silentReport("The node with " +  tagName + "tag wasn't found. Make sure that you applied a" + K.lineSeparator + "search before using select command");
			return result;
		}
		for (int i = 0; i < list.getLength(); i++) {
			nod = list.item(i);
			if (nod == null) {
				Error.report("The node with " + tagName + " tag wasn't found");
			} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) nod;
				if (elem.getAttribute(attributeName).equals("NONE")) {
					continue;
				}
				String solIdentifier = elem.getAttribute(attributeName);
				//we found the desired search solution
				if (solIdentifier.equals(solutionIdentifier)) {
					// using XPath for direct access to the desired node
					XPathFactory factory = XPathFactory.newInstance();
					XPath xpath = factory.newXPath();
					String s = null;
					Object result1;
					s = xpathExpression;
					try {
						result1 = xpath.evaluate(s, nod, XPathConstants.NODESET);
						if (result1 != null) {
							NodeList nodes = (NodeList) result1;
							nod = nodes.item(0);
							result = (Element)nod;
							break;
						}
						else {
							String output = FileUtil.getFileContent(K.maude_out);
							Error.report("Unable to parse Maude's search results:\n" + output);
						}

					} catch (XPathExpressionException e) {
						Error.report("XPathExpressionException " + e.getMessage());
					}
				}
			}
		}
		return result;
	}
	
	/* retrieve the solution (a node in the xml file denoted by fileName) specified by its solution-number attribute 
	or retrieve the term node from a node in the search graph obtained from a search command */
	public static Element getSearchSolution(String fileName, String solutionIdentifier) {
		Element result = null;
		File input = new File(fileName);
		Document doc = XmlUtil.readXML(input);
		
		//if solutionIdentifier represents a numeric value that it identifies a solution (specified by its solution-number attribute) from the search-result
		//otherwise solutionIdentifier identifies an id of a node from the search graph
		boolean isNumber = Utils.isNumber(solutionIdentifier);
		if (isNumber) {
			result = getTerm(doc, "search-result", "solution-number", "substitution/assignment/term[2]", solutionIdentifier);
		}
		else {
			result = getTerm(doc, "node", "id", "data/term", solutionIdentifier);
		}
		return result;
	}
	
	//create a xml document that contains the elem node (should be in the form a xml file obtained after a maude rewrite command) 
	public static Document createXmlRewriteForm(Element elem) {
		Document doc = null;
		
		DocumentBuilderFactory docFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder docBuilder;
		try {
			docBuilder = docFactory.newDocumentBuilder();
			// root element
			doc = docBuilder.newDocument();
			Element rootElement = doc.createElement("maudeml");
			doc.appendChild(rootElement);
			
			Element resultNode = doc.createElement("result");
			resultNode.appendChild(doc.adoptNode(elem.cloneNode(true)));
			rootElement.appendChild(resultNode);
			
			return doc;
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		}
 
		return doc;
	}

}
