package org.kframework.krun;

import org.kframework.utils.file.FileUtil;
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

	public static Document readXMLFromFile(String fileName) {
        try (InputStream byteStream = new BufferedInputStream(new FileInputStream(fileName))) {
            return readXML(new InputSource(byteStream));
        }catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static Document readXMLFromString(String s) {
        try (Reader reader = new StringReader(s)) {
            return readXML(new InputSource(reader));
        }catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

	public static Document readXML(InputSource input) {
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		Document doc = null;
		try {
			DocumentBuilder builder = dbf.newDocumentBuilder();
			doc = builder.parse(input);
		} catch (ParserConfigurationException | IOException | SAXException e) {
			e.printStackTrace();

			org.kframework.utils.Error.report("Error while reading XML:" + e.getMessage());
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

	// write the XML document to disk
	public static void serializeXML(Node doc, String fileName) {
        Source xmlSource = new DOMSource(doc);
		try (OutputStream outStream = new BufferedOutputStream(new FileOutputStream(fileName))) {
            Result result = new StreamResult(outStream);
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            // transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
            transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "1");
            transformer.transform(xmlSource, result);
		} catch (TransformerFactoryConfigurationError factoryError) {
			// factoryError.printStackTrace();
			org.kframework.utils.Error.report("Error creating TransformerFactory:" + factoryError.getMessage());
		} catch (TransformerException transformerError) {
			// transformerError.printStackTrace();
			org.kframework.utils.Error.report("Error transforming document:" + transformerError.getMessage());
		} catch (IOException ioException) {
			// ioException.printStackTrace();
			org.kframework.utils.Error.report("Error while serialize XML:" + ioException.getMessage());
		}
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
		NodeList list;
		Node nod;
		
		list = doc.getElementsByTagName(tagName);
		if (list.getLength() == 0) {
			org.kframework.utils.Error.silentReport("The node with " +  tagName + "tag wasn't found. Make sure that you applied a" + K.lineSeparator + "search before using select command");
			return result;
		}
		for (int i = 0; i < list.getLength(); i++) {
			nod = list.item(i);
			if (nod == null) {
				org.kframework.utils.Error.report("The node with " + tagName + " tag wasn't found");
			} else if (nod.getNodeType() == Node.ELEMENT_NODE) {
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
					String s = xpathExpression;
					Object result1;
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
							org.kframework.utils.Error.report("Unable to parse Maude's search results:\n" + output);
						}

					} catch (XPathExpressionException e) {
						org.kframework.utils.Error.report("XPathExpressionException " + e.getMessage());
					}
                }
			}
		}
		return result;
	}
}
