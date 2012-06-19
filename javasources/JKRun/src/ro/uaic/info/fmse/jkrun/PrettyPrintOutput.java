package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.apache.commons.cli.CommandLine;
import org.fusesource.jansi.AnsiConsole;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class PrettyPrintOutput {
	
	private CommandLine cmd;
	
	public static final int indent = 2;
	
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
	
	public void preprocessDoc(File file, String processedFile) {
		Document doc = readXML(file);
		
		Node root = doc.getDocumentElement();
		preprocessElement((Element)root);
		
		XmlUtil.serializeXML(doc, processedFile);
	}
	
	public void preprocessElement(Element node) {
		NodeList list = null;

		list = node.getChildNodes();
		if (list != null && list.getLength() > 0) {
			for (int i = 0; i < list.getLength(); i++) {
				if (list.item(i).getNodeType() == Node.ELEMENT_NODE) {
					preprocessElement((Element) list.item(i));
				}
			}
			if (node.hasAttribute("op") && node.hasAttribute("sort")) {
				applyRules(node);
			}
		}
	}
	
	private static void applyRules(Element node) {
		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");
		
		//rule 1
		if (sort.equals("KItem") && op.equals("_`(_`)")) {
			Node parent = node.getParentNode();
			Node nextSibling = XmlUtil.getNextSiblingElement(node);
			
			ArrayList<Element> list = XmlUtil.getChildElements(node);
			Element firstChild = list.get(0);
			String sort_ = firstChild.getAttribute("sort");
			if (sort_.equals("KLabel")) {
				for (int i = 1; i < list.size(); i++) {
					firstChild.appendChild(list.get(i));
				}
				parent.insertBefore(firstChild, nextSibling);
				parent.removeChild(node);
			}
		}
		
		//rule 2
		if (sort.equals("NeList`{K`}") && op.equals("_`,`,_")) {
			Node parent = node.getParentNode();
			Node nextSibling = XmlUtil.getNextSiblingElement(node);
			
			ArrayList<Element> list = XmlUtil.getChildElements(node);
			if (list.size() >= 2) {
				for (Element elem: list) {
					parent.insertBefore(elem, nextSibling);
				}
				parent.removeChild(node);
			}
		}
		
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
						//return processElement((Element) child.item(i));
						return print((Element) child.item(i), false, 0, ANSI_NORMAL);
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
						//return processElement((Element) nod);
						return print((Element) nod, false, 0, ANSI_NORMAL);
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
				StringBuilder aux = new StringBuilder();
				NodeList ch = node.getChildNodes();
				for (int j = 0; j < ch.getLength(); j++) {
					if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
						elements.add(processElement((Element) ch.item(j)));
					}
				}
				op = op.replaceAll("_", " ");
				for (int i = 0; i < elements.size(); i++) {
					String s = elements.get(i);
					s = s.trim();
					if (i == elements.size() - 1) {
						aux.append(s);
					} else {
						aux.append(s);
						aux.append(op);
					}
				}
                result = aux.toString();
			}
			return result;
		}
		if (op.equals("#istream`(_`)") || op.equals("#ostream`(_`)")) { // the istream and ostream cells are ignored
			result = "";
			return result;
		}
		if (sort.equals("BagItem") || sort.equals("MapItem") || sort.equals("ListItem")) {
			List<String> elements = new ArrayList<String>();
			NodeList ch = node.getChildNodes();
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					elements.add(processElement((Element) ch.item(j)));
				}
			}
			op = op.replaceAll("`", "");
			String initOp = op;
			int index = 0;
		    int count = 0;
		    StringBuilder sb = new StringBuilder(op);
			while (index != -1) {
				index = sb.indexOf("_", index);
				if (index != -1) {
					String s = (String)elements.get(count);
					s = s.trim();
					if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
						if (count == 0) {
							s = s + " ";
						}
					}
					if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
						if (count == 1) {
							s = " " + s;
						}
					}
					sb.insert(index, s);
					index += s.length();
					sb = sb.deleteCharAt(index);
					count++;
					op = sb.toString();
					if (op.equals(initOp)) {
				    	op = s;
				    }
				}
			}
			result = op;
		}
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
				if (sort.equals("NeMap") || sort.equals("NeList"))
					sb.append("\n");
			}
			result = sb.toString();	
		}
		if (sort.equals("List")) {
			List<String> elements = new ArrayList<String>();
			StringBuilder sb = new StringBuilder();
			NodeList ch = node.getChildNodes();
			op = op.replaceAll("`", "");
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
				int index = 0;
			    int count = 0;
			    StringBuilder sb_ = new StringBuilder(op);
				while (index != -1) {
					index = sb_.indexOf("_", index);
					if (index != -1) {
						String s = (String)elements.get(count);
						sb_.insert(index, s);
						index += s.length();
						sb_ = sb_.deleteCharAt(index);
						count++;
						op = sb_.toString();
					}
				}
				result = op;
			}
		}
		if (sort.equals("KLabel") && !op.equals("'.List`{\",\"`}")) {
			NodeList ch = node.getChildNodes();
			List<String> elements = new ArrayList<String>();
			for (int j = 0; j < ch.getLength(); j++) {
				if (ch.item(j).getNodeType() == Node.ELEMENT_NODE) {
					Element child = (Element) ch.item(j);
				    elements.add(processElement(child));
				}
			}
			op = op.replaceAll("`", "");
			char firstCh = op.charAt(0);
			if ((firstCh == '#') || (firstCh == '\'')) {
				op = op.substring(1);
			}
			//System.out.print("Before: Op=" + op);
			StringBuilder sb = new StringBuilder(op);
			int index = 0;
			while (index != -1) {
				index = sb.indexOf("_", index);
				if (index != -1) {
					if (index == 0) {
						sb.insert(index + 1, " ");
						index += "-".length();
					} else if (index == sb.length() - 1) {
						sb.insert(index, " ");
						index += 2;
					} else {
						sb = sb.insert(index + 1, " ");
						sb = sb.insert(index, " ");
						index += 2;
					}
				}
			}
			op = sb.toString();
			index = 0;
		    int count = 0;
		    StringBuilder sb_ = new StringBuilder(op);
			while (index != -1) {
				index = sb_.indexOf("_", index);
				if (index != -1) {
					String s = (String)elements.get(count);
					s = s.trim();
					sb_.insert(index, s);
					index += s.length();
					sb_ = sb_.deleteCharAt(index);
					count++;
					op = sb_.toString();
				}
			}
			result = op;
			//System.out.println(" After: Op=" + op);
		}
		if (sort.equals("KLabel") && op.equals("'.List`{\",\"`}")) {
			Element previous = XmlUtil.getPreviousSiblingElement(node);
			// if the node has siblings
			if (previous != null) {
				result = "";
			}
			else {
				result = ".";
			}
		}
		if ((sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("--Int_"))) {
		//if ((sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("--Int_")) || (sort.equals("ListItem") && op.equals("ListItem"))) {
		//if ((sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("--Int_"))) {
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
			if (sort.equals("#NzInt") && op.equals("--Int_")) {
				result = "-" + processElement(firstChild);
			} else {
				result = processElement(firstChild);
			}
			
		}
		// TODO: what other sorts that may appear should be added here? 
		if (sort.equals("#Zero") || sort.equals("#Bool")) {
			result = op;
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
			result = " " + result;
		}
		if (op.equals(".")) {
			result = ".";
		}

		/* else { //default case result = convertNodeToString(node); } */

		return result;
	}
	
	private static String print(Element node, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		//StringBuilder sb;
		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");
		ArrayList<Element> list = XmlUtil.getChildElements(node);
		
		if (sort.equals("BagItem") && op.equals("<_>_</_>")) {
			sb = new StringBuilder();
		   	sb.append(prettyPrint("<", true, whitespace, ANSI_GREEN));
		   	sb.append(prettyPrint(print(list.get(0), false, 0, ANSI_NORMAL), false, 0, ANSI_GREEN));
		   	sb.append(prettyPrint(">", false, 0, ANSI_GREEN));
		   	for (int i = 1; i < list.size() - 1; i++) {
		   		Element child = list.get(i);
		   		sb.append(prettyPrint(print(child, false, 0, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL));
		   	}
		   	sb.append(prettyPrint("</", true, whitespace, ANSI_GREEN));
		   	String str = prettyPrint(print(list.get(list.size() - 1), false, 0, ANSI_NORMAL), false, 0, ANSI_GREEN);
		   	//sb.append(prettyPrint(print(list.get(list.size() - 1), false, 0, ANSI_NORMAL), false, 0, ANSI_GREEN));
		   	sb.append(str);
		   	sb.append(prettyPrint(">", false, 0, ANSI_GREEN));
		}
		if (sort.equals("BagItem") && !op.equals("<_>_</_>")) {
			sb = new StringBuilder();
			for (int i = 0; i < list.size(); i++) {
		   		Element child = list.get(i);
		   		sb.append(prettyPrint(print(child, false, 0, ANSI_NORMAL), false, 0, ANSI_NORMAL));
		   	}
		}
		if (sort.equals("CellLabel") || sort.equals("K")) {
			sb = new StringBuilder();
			//sb = new StringBuilder(op);
			if (op.indexOf("_") != -1) {
				List<String> elements = new ArrayList<String>();
				StringBuilder aux = new StringBuilder();
				for (int i = 0; i < list.size(); i++) {
			   		    Element child = list.get(i);
			   		    elements.add(print(child, false, 0, ANSI_NORMAL));   
				}
				op = op.replaceAll("_", " ");
				for (int i = 0; i < elements.size(); i++) {
					String s = elements.get(i);
					s = s.trim();
					if (i == elements.size() - 1) {
						aux.append(s);
					} else {
						aux.append(s);
						aux.append(op);
					}
				}
                sb.append(aux);
			}
			sb.append(op);
		}
		if (op.equals("#istream`(_`)") || op.equals("#ostream`(_`)")) { // the istream and ostream cells are ignored
			sb = new StringBuilder();
			sb.append("");
		}
		if (sort.equals("MapItem") || sort.equals("ListItem")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    elements.add(print(child, lineskip, whitespace, ANSI_NORMAL));   
		    }
			op = op.replaceAll("`", "");
			String initOp = op;
			int index = 0;
		    int count = 0;
		    StringBuilder sb_ = new StringBuilder(op);
			while (index != -1) {
				index = sb_.indexOf("_", index);
				if (index != -1) {
					String s = (String)elements.get(count);
					s = s.trim();
					if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
						if (count == 0) {
							s = s + " ";
						}
					}
					if (sort.equals("MapItem") && initOp.equals("_|->_")) { // for pretty-printing
						if (count == 1) {
							s = " " + s;
						}
					}
					sb_.insert(index, s);
					index += s.length();
					sb_ = sb_.deleteCharAt(index);
					count++;
					op = sb_.toString();
					if (op.equals(initOp)) {
				    	op = s;
				    }
				}
			}
			sb.append(op);
		}
		if (sort.equals("NeBag") || sort.equals("NeMap") || sort.equals("NeList")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			StringBuilder sb_ = new StringBuilder();
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    elements.add(print(child, true, whitespace + indent, ANSI_NORMAL));   
		    }
			for (String s : elements) {
				sb_.append(s);
				//if (sort.equals("NeMap") || sort.equals("NeList"))
					//sb_.append("\n");
			}
			sb.append(sb_);	
		}
		if (sort.equals("List")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			StringBuilder sb_ = new StringBuilder();
			op = op.replaceAll("`", "");
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    elements.add(print(child, false, whitespace + indent, ANSI_NORMAL));   
		    }
			if (K.io) {
				for (String s : elements) {
					sb_.append(s);
				}
				sb.append(sb_);
			} else {
				int index = 0;
			    int count = 0;
			    StringBuilder sb1 = new StringBuilder(op);
				while (index != -1) {
					index = sb1.indexOf("_", index);
					if (index != -1) {
						String s = (String)elements.get(count);
						sb1.insert(index, s);
						index += s.length();
						sb1 = sb1.deleteCharAt(index);
						count++;
						op = sb1.toString();
					}
				}
				sb.append(op);
			}
		}
		if (sort.equals("KLabel") && !op.equals("'.List`{\",\"`}")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    elements.add(print(child, false, 0, ANSI_NORMAL));   
		    }
			op = op.replaceAll("`", "");
			char firstCh = op.charAt(0);
			if ((firstCh == '#') || (firstCh == '\'')) {
				op = op.substring(1);
			}
			//System.out.print("Before: Op=" + op);
			StringBuilder sb_ = new StringBuilder(op);
			int index = 0;
			while (index != -1) {
				index = sb_.indexOf("_", index);
				if (index != -1) {
					if (index == 0) {
						sb_.insert(index + 1, " ");
						index += "-".length();
					} else if (index == sb_.length() - 1) {
						sb_.insert(index, " ");
						index += 2;
					} else {
						sb_ = sb_.insert(index + 1, " ");
						sb_ = sb_.insert(index, " ");
						index += 2;
					}
				}
			}
			op = sb_.toString();
			index = 0;
		    int count = 0;
		    StringBuilder sb1 = new StringBuilder(op);
			while (index != -1) {
				index = sb1.indexOf("_", index);
				if (index != -1) {
					String s = (String)elements.get(count);
					s = s.trim();
					sb1.insert(index, s);
					index += s.length();
					sb1 = sb1.deleteCharAt(index);
					count++;
					op = sb1.toString();
				}
			}
			sb.append(op);
			//System.out.println(" After: Op=" + op);
		}
		if (sort.equals("KLabel") && op.equals("'.List`{\",\"`}")) {
			sb = new StringBuilder();
			Element previous = XmlUtil.getPreviousSiblingElement(node);
			// if the node has siblings
			if (previous != null) {
				sb.append("");
			}
			else {
				sb.append(".");
			}
		}
		if ((sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("--Int_"))) {
			sb = new StringBuilder();
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
			if (sort.equals("#NzInt") && op.equals("--Int_")) {
				sb = new StringBuilder();
				sb.append("-" + print(firstChild, false, 0, ANSI_NORMAL)); 
			} else {
				sb.append(print(firstChild, false, 0, ANSI_NORMAL));
			}
		}
		// TODO: what other sorts that may appear should be added here? 
		if (sort.equals("#Zero") || sort.equals("#Bool")) {
			sb = new StringBuilder();
			sb.append(op);
		}
		if (sort.equals("#NzNat") && op.equals("sNat_")) {
			sb = new StringBuilder();
			sb.append(node.getAttribute("number"));
		}
		if (sort.equals("#Char") || sort.equals("#String")) {
			sb = new StringBuilder();
			String parts[];
			parts = op.split("\"");
			sb.append(parts[1]);
			if (sb.toString().startsWith("#")) {
				sb.append("\"" + sb + "\"");
			}
			//sb.append(" ");
		}
		if (op.equals(".")) {
			sb = new StringBuilder();
			sb.append(".");
		}
		
		return sb.toString();
	}
	
	private static String prettyPrint(String text, boolean lineskip, int whitespace, String color) {
		StringBuilder output = new StringBuilder();
		StringBuilder aux;
		AnsiConsole.systemInstall();
		//newline
		if (lineskip) {
			output.append(K.lineSeparator);
		}
		if (whitespace > 0) {
			String space = XmlUtil.buildWhitespace(whitespace);
			output.append(space);
		}
		/*if (K.color) {
			if (!color.equals("ANSI_NORMAL")) {
				output.append(color);
			    output.append(text);
			    output.append("ANSI_NORMAL");
			}
			else if (text.indexOf("|->") != -1) {
				aux = new StringBuilder();
                aux = XmlUtil.colorSymbol(text, "|->", PrettyPrintOutput.ANSI_PURPLE);
                output.append(aux);
			}
			else if (text.indexOf("|->") != -1) {
				aux = new StringBuilder();
				aux = XmlUtil.colorSymbol(text, "~>", PrettyPrintOutput.ANSI_BLUE);
				output.append(aux);
			}
			else {
				output.append(text);
			}
		}
		else {
			output.append(text);
		}*/
		output.append(text);
		
		return output.toString();
	}
	
	public void setCmd(CommandLine cmd) {
		this.cmd = cmd;
	}

	public CommandLine getCmd() {
		return cmd;
	}
	

}