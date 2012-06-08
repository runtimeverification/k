package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.apache.commons.cli.CommandLine;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class PrettyPrintOutput {
	
	private CommandLine cmd;
	
	public static final String ANSI_NORMAL = "\u001b[0m";
	
    public static final String ANSI_BLACK = "\u001B[30m";
    public static final String ANSI_RED = "\u001B[31m";
    public static final String ANSI_GREEN = "\u001B[32m";
    public static final String ANSI_YELLOW = "\u001B[33m";
    public static final String ANSI_BLUE = "\u001B[34m";
    public static final String ANSI_PURPLE = "\u001B[35m";
    public static final String ANSI_CYAN = "\u001B[36m";
    public static final String ANSI_WHITE = "\u001B[37m";
    
    public PrettyPrintOutput() {
    	this.cmd = null;
    }
    
    public PrettyPrintOutput(CommandLine cmd_) {
    	this.cmd = cmd_;
    }
	
	// Function to read DOM Tree from File
	public Document readXML(File f) {

		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		Document doc = null;
		try {
			builder = dbf.newDocumentBuilder();
			InputSource input = new InputSource(new FileInputStream(f));
			doc = builder.parse(input);
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return doc;
	}

	/* return the value for the attribute attrName of result tag */
	public String getResultTagAttr(File file, String attrName) {
		Document doc = readXML(file);
		NodeList list = doc.getElementsByTagName("result");
		Node nod = list.item(0);

		if (nod == null) {
			Error.report("Pretty Print Output: The node with result tag wasn't found");
		} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
			Element elem = (Element) nod;
			String attr = elem.getAttribute(attrName);
			return attr;
		}
		return null;
	}

	public String getSearchTagAttr(File file, String attrName) {
		Document doc = readXML(file);
		NodeList list = doc.getElementsByTagName("search-result");
		Node nod = list.item(0);

		if (nod == null) {
			Error.report("Pretty Print Output: The node with search-result tag wasn't found");
		} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
			Element elem = (Element) nod;
			String attr = elem.getAttribute(attrName);
			return attr;
		}
		return null;
	}

	public String processDoc(File file) {
		Document doc = readXML(file);
		NodeList list = null;
		Node nod = null;

		if (K.maude_cmd.equals("erewrite") && !(cmd.hasOption("xsearch-pattern"))) {
			list = doc.getElementsByTagName("result");
			nod = list.item(0);
			if (nod == null) {
				Error.report("Pretty Print Output: The node with result tag wasn't found");
			} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) nod;
				NodeList child = elem.getChildNodes();
				for (int i = 0; i < child.getLength(); i++) {
					if (child.item(i).getNodeType() == Node.ELEMENT_NODE) {
						return processElement((Element) child.item(i));
					}
				}
			}
		} else if (K.maude_cmd.equals("search") || cmd.hasOption("xsearch-pattern")) {
			list = doc.getElementsByTagName("search-result");
			nod = list.item(0);
			if (nod == null) {
				Error.report("Pretty Print Output: The node with search-result tag wasn't found");
			} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) nod;
				if (elem.getAttribute("solution-number").equals("NONE")) {
					String output = FileUtil.getFileContent(K.maude_out);
					Error.report("Unable to parse Maude's search results:\n" + output);
				}
				// using XPath for direct access to the desired node
				XPathFactory factory2 = XPathFactory.newInstance();
				XPath xpath2 = factory2.newXPath();
				String s2 = "substitution/assignment/term[2]";
				Object result2;
				try {
					result2 = xpath2.evaluate(s2, nod, XPathConstants.NODESET);
					if (result2 != null) {
						NodeList nodes2 = (NodeList) result2;
						nod = nodes2.item(0);
						return processElement((Element) nod);
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
		return null;
	}

	private static String processElement(Element node) {
		String result = new String();
		// the default value to use when none of the below rules can be applied
		// result = convertNodeToString(node);

		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");

		if (sort.equals("CellLabel") || sort.equals("K")) {
			result = op;
			if (op.indexOf("_") != -1) {
				List<String> elements = new ArrayList<String>();
				NodeList ch = node.getChildNodes();
				for (int j = 0; j < ch.getLength(); j++) {
					if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
						elements.add(processElement((Element) ch.item(j)));
					}
				}
				for (int i = 0; i < elements.size(); i++) {
					String s = elements.get(i);
					op = op.replaceFirst("_", s);
				}
				result = op;

			}
			return result;
		}
		if (op.equals("#istream`(_`)") || op.equals("#ostream`(_`)") || op.equals("ListItem")) { // the istream and ostream cells are ignored
			result = "";
			return result;
		}
		// BagItem or MapItem or NeList sort
		if (sort.equals("BagItem") || sort.equals("MapItem")) {
			List<String> elements = new ArrayList<String>();
			NodeList ch = node.getChildNodes();
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					elements.add(processElement((Element) ch.item(j)));
				}
			}
			String initOp = op;
			for (int i = 0; i < elements.size(); i++) {
				String s = elements.get(i);
				if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
					if (i == 0) {
						s = s + " ";
					}
				}
				if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
					if (i == 1) {
						s = " " + s;
					}
				}
				op = op.replaceFirst("_", s);
			}
			result = op;
		}
		if (sort.equals("List")) {
			List<String> elements = new ArrayList<String>();
			StringBuilder sb = new StringBuilder();
			NodeList ch = node.getChildNodes();
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					elements.add(processElement((Element) ch.item(j)));
				}
			}
			if (K.io) {
				for (String s : elements) {
					sb.append(s);
				}
				result = sb.toString();
			} else {
				for (int i = 0; i < elements.size(); i++) {
					String s = elements.get(i);
					op = op.replaceFirst("_", s);
				}
				result = op;
			}
		}
		// NeBag or NeMap sort
		if (sort.equals("NeBag") || sort.equals("NeMap") || sort.equals("NeList")) {
			List<String> elements = new ArrayList<String>();
			StringBuilder sb = new StringBuilder();
			NodeList ch = node.getChildNodes();
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					elements.add(processElement((Element) ch.item(j)));
				}
			}
			for (String s : elements) {
				sb.append(s);
				if (sort.equals("NeMap"))
					sb.append("\n");
			}
			result = sb.toString();
		}
		if (sort.equals("KItem") && op.equals("_`(_`)")) {
			NodeList ch = node.getChildNodes();
			// used for counting the child nodes that are of Element type
			int count = 0;
			Element firstChild = null;
			Element secondChild = null;
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					Element elem = (Element) ch.item(j);
					if (count == 0) {
						firstChild = elem;
					}
					if (count == 1) {
						secondChild = elem;
					}
					count++;
				}
			}
			if (secondChild.getAttribute("sort").equals("List`{K`}")) {
				result = processElement(firstChild);
				// System.out.println("result="+result);
			} else {
				List<String> elements = new ArrayList<String>();
				elements.add(processElement(firstChild));
				elements.add(processElement(secondChild));
				for (String s : elements)
					op = op.replaceFirst("_", s);
				result = op;
			}
		}
		if ((sort.equals("KLabel") && op.equals("#_")) || (sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("-Int_"))) {
			NodeList ch = node.getChildNodes();
			// used for counting the child nodes that are of Element type
			int count = 0;
			Element firstChild = null;
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					Element elem = (Element) ch.item(j);
					if (count == 0) {
						firstChild = elem;
						break;
					}

				}
			}
			if (sort.equals("#NzInt") && op.equals("-Int_")) {
				result = "-" + processElement(firstChild);
			} else {
				result = processElement(firstChild);
			}
		}
		/* if (sort.equals("KLabel") && !op.equals("#_")) { result = op; } */
		if (sort.equals("#Zero") && op.equals("0")) {
			result = "0";
		}
		if (sort.equals("#NzNat") && op.equals("sNat_")) {
			result = node.getAttribute("number");
		}
		if (sort.equals("#Char") || sort.equals("#String")) {
			String parts[];
			parts = op.split("\"");
			result = parts[1];
			if (result.startsWith("#")) {
				result = "\"" + result + "\"";
			}
		}
		if (op.equals(".")) {
			result = ".";
		}

		/* else { //default case result = convertNodeToString(node); } */

		return result;
	}

	public static String convertNodeToString(Node node) {
		try {
			Transformer t = TransformerFactory.newInstance().newTransformer();
			t.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
			StringWriter sw = new StringWriter();
			t.transform(new DOMSource(node), new StreamResult(sw));
			return sw.toString();
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return null;
	}

	public void setCmd(CommandLine cmd) {
		this.cmd = cmd;
	}

	public CommandLine getCmd() {
		return cmd;
	}

}