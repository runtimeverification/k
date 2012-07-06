package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

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

public class PrettyPrintOutput {
	
	private CommandLine cmd;
	
	public static final int indent = 1;
	
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

	/* return the value for the attribute attrName of result tag */
	public String getResultTagAttr(File file, String attrName) {
		Document doc = XmlUtil.readXML(file);
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

	/* return the value for the attribute attrName of search-result tag */
	public String getSearchTagAttr(File file, String attrName) {
		Document doc = XmlUtil.readXML(file);
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
	
	public void preprocessDoc(String fileName, String processedFile) {
		File input = new File(fileName);
		Document doc = XmlUtil.readXML(input);
		
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

	public String processDoc(String fileName) {
		File input = new File(fileName);
		Document doc = XmlUtil.readXML(input);
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
	
	private static String print(Element node, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");
		ArrayList<Element> list = XmlUtil.getChildElements(node);
		
		if (sort.equals("BagItem") && op.equals("<_>_</_>")) {
			sb = new StringBuilder();
		   	sb.append(prettyPrint("<", true, whitespace, ANSI_GREEN));
		   	sb.append(prettyPrint(print(list.get(0), false, whitespace, ANSI_GREEN), false, whitespace, ANSI_GREEN));
		   	sb.append(prettyPrint(">", false, 0, ANSI_GREEN));
		   	for (int i = 1; i < list.size() - 1; i++) {
		   		Element child = list.get(i);
		   		sb.append(prettyPrint(print(child, true, whitespace + indent, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL));
		   	}
		   	sb.append(prettyPrint("</", true, whitespace, ANSI_GREEN));
		   	sb.append(prettyPrint(print(list.get(list.size() - 1), false, whitespace, ANSI_GREEN), false, whitespace, ANSI_GREEN));
		   	sb.append(prettyPrint(">", false, 0, ANSI_GREEN));
		   	return sb.toString();
		}
		if (sort.equals("BagItem") && !op.equals("<_>_</_>")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = FileUtil.countUnderscores(op);
			
			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < n; i++) {
					Element child = list.get(i);
					String prettyStr = prettyPrint(print(child, true, whitespace + indent, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL);
					if (prettyStr.length() > 0) {
						elements.add(prettyStr);
					}
				}
				sb.append(op);
				if (elements.size() > 0) {
					sb.append("(");
				}
				for (int i = 0; i < elements.size(); i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (elements.size() > 0) {
					sb.append(")");
				}
			}
			else if (m < n && n > 0 && m > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
		   		    Element child = list.get(i);
		   		    elements.add(prettyPrint(print(child, true, whitespace + indent, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL));
			    }
				StringBuilder sb1 = FileUtil.replaceAllUnderscores(op, elements);
				sb.append(sb1);
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append("(");
				}
				for (int i = m; i < n; i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append(")");
				}
			}
			return sb.toString();
			
		}
		if (sort.equals("CellLabel")) {
			sb.append(op);
			return sb.toString();
		}
		if (sort.equals("K")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
            int m = FileUtil.countUnderscores(op);
			
			//postprocess
			op = postProcessElement(node, op, sort);
			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < n; i++) {
					Element child = list.get(i);
					String prettyStr = prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL);
					if (prettyStr.length() > 0) {
						elements.add(prettyStr);
					}
				}
				sb.append(op);
				if (elements.size() > 0) {
					sb.append("(");
				}
				for (int i = 0; i < elements.size(); i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
	                    sb.append(", ");
					}
				}
				if (elements.size() > 0) {
					sb.append(")");
				}
			}
			//like in the case of an associative operator (<term op="_~>_" sort="K">)
			else if (m < n && n > 0 && m > 0) {
				List<String> elements = new ArrayList<String>();
				StringBuilder aux = new StringBuilder();
				for (int i = 0; i < list.size(); i++) {
					Element child = list.get(i);
					elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
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
			//like in the case of <term op="var`{K`}`(_`)" sort="K">
			else if (m == n) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
					Element child = list.get(i);
					String elem = prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL);
					elements.add(elem.trim());
				}
				StringBuilder sb_ = new StringBuilder(op);
				int index = 0;
				//insert around each "_" additional space depending on "_" position  
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
				StringBuilder sb1 = new StringBuilder(op);
				//replace each "_" with its children representation
			    sb1 = FileUtil.replaceAllUnderscores(op, elements);
			    op = sb1.toString();
				sb.append(op);
			}
			return sb.toString();
	}
		
		if (sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("SetItem")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = FileUtil.countUnderscores(op);
			
			//postprocess
			op = postProcessElement(node, op, sort);
			
			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < n; i++) {
					Element child = list.get(i);
					String prettyStr = new String();
				    prettyStr = prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL);
					
					if (prettyStr.length() > 0) {
						elements.add(prettyStr);
					}
				}
				sb.append(op);
				if (elements.size() > 0) {
					sb.append("(");
				}
				for (int i = 0; i < elements.size(); i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (elements.size() > 0) {
					sb.append(")");
				}
			}
			else if (m < n && n > 0 && m > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
		   		    Element child = list.get(i);
		   		    elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
			    }
				StringBuilder sb1 = FileUtil.replaceAllUnderscores(op, elements);
				sb.append(sb1);
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append("(");
				}
				for (int i = m; i < n; i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append(")");
				}
			}
            else {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
					Element child = list.get(i);
					elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
				}
				String initOp = op;
				int index = 0;
				int count = 0;
				StringBuilder sb_ = new StringBuilder(op);
				while (index != -1) {
					index = sb_.indexOf("_", index);
					if (index != -1) {
						String s = (String) elements.get(count);
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
			return sb.toString();
		}
		if (sort.equals("NeBag") || sort.equals("NeMap") || sort.equals("NeList")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			StringBuilder sb_ = new StringBuilder();
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    if (sort.equals("NeMap") || sort.equals("NeList")) {
	   		    	elements.add(prettyPrint(print(child, true, whitespace + indent, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL));
	   		    }
	   		    else {
	   		    	elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
	   		    }
		    }
			for (String s : elements) {
				sb_.append(s);
			}
			sb.append(sb_);	
			return sb.toString();
		}
		if (sort.equals("List")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			StringBuilder sb_ = new StringBuilder();
			//postprocess
			op = postProcessElement(node, op, sort);
			
			for (int i = 0; i < list.size(); i++) {
	   		    Element child = list.get(i);
	   		    elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));   
		    }
		    sb_ = new StringBuilder(op);
			int index = 0;
			//insert around each "_" additional space depending on "_" position  
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
			StringBuilder sb1 = new StringBuilder(op);
			//replace each "_" with its children representation
		    sb1 = FileUtil.replaceAllUnderscores(op, elements);
		    op = sb1.toString();
			sb.append(op);
			return sb.toString();
		}
		if ((sort.equals("KLabel") && !op.equals("'.List`{\",\"`}") )
			|| sort.equals("#ModelCheckResult") || sort.equals("#TransitionList") || sort.equals("#Transition") || sort.equals("#ModelCheckerState")
			) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = FileUtil.countUnderscores(op);
			
			//postprocess
			op = postProcessElement(node, op, sort);
			
			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < n; i++) {
					Element child = list.get(i);
					String prettyStr = prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL);
					if (prettyStr.length() > 0) {
						elements.add(prettyStr);
					}
				}
				sb.append(op);
				if (elements.size() > 0) {
					sb.append("(");
				}
				for (int i = 0; i < elements.size(); i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (elements.size() > 0) {
					sb.append(")");
				}
			}
			else if (m < n && n > 0 && m > 0) {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
		   		    Element child = list.get(i);
		   		    elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
			    }
				StringBuilder sb1 = FileUtil.replaceAllUnderscores(op, elements);
				sb.append(sb1);
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append("(");
				}
				for (int i = m; i < n; i++) {
					sb.append(elements.get(i));
					if (i != elements.size() - 1) {
                        sb.append(", ");
					}
				}
				if (!(n - m == 1 && elements.get(m).length() == 0)) {
					sb.append(")");
				}
			}
            else {
				List<String> elements = new ArrayList<String>();
				for (int i = 0; i < list.size(); i++) {
					Element child = list.get(i);
					elements.add(prettyPrint(print(child, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL));
				}
				StringBuilder sb_ = new StringBuilder(op);
				int index = 0;
				//insert around each "_" additional space depending on "_" position  
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
				//replace each "_" with its child representation
				while (index != -1) {
					index = sb1.indexOf("_", index);
					if (index != -1) {
						if (count >= elements.size()) {
							break;
						}
						String s = (String) elements.get(count);
						s = s.trim();
						sb1.insert(index, s);
						index += s.length();
						sb1 = sb1.deleteCharAt(index);
						count++;
						op = sb1.toString();
					}
				}
				sb.append(op);
			}
			return sb.toString();
		}
		if (sort.equals("KLabel") && op.equals("'.List`{\",\"`}")) {
			sb = new StringBuilder();
			Element previous = XmlUtil.getPreviousSiblingElement(node);
			// if the node has siblings
			/*if (previous != null) {
				sb.append("");
			}
			else {
				sb.append(".");
			}*/
			sb.append(".");
			return sb.toString();
		}
		if ((sort.equals("#Id") && op.equals("#id_")) || (sort.equals("#NzInt") && op.equals("--Int_"))) {
			sb = new StringBuilder();
			Element firstChild = list.get(0);
			String s = prettyPrint(print(firstChild, false, whitespace, ANSI_NORMAL), false, whitespace, ANSI_NORMAL);
			if (sort.equals("#NzInt") && op.equals("--Int_")) {
				sb = new StringBuilder();
				sb.append("-" + s); 
			} else {
				//eliminate the apostrophes
				String parts[];
				parts = s.split("\"");
				sb.append(parts[1]);
			}
			return sb.toString();
		}
		// TODO: what other sorts(builtins) that may appear should be added here? 
		if (sort.equals("#Zero") || sort.equals("#Bool") || sort.equals("#Char") || sort.equals("#String") || sort.equals("#Int") || sort.equals("#Float")) {
			sb = new StringBuilder();
			sb.append(op);
			return sb.toString();
		}
		if (sort.equals("#NzNat") && op.equals("sNat_")) {
			sb = new StringBuilder();
			sb.append(node.getAttribute("number"));
			return sb.toString();
		}
		if (op.equals(".")) {
			sb = new StringBuilder();
			sb.append(".");
			return sb.toString();
		}
		
		return sb.toString();
	}
	
	private static String prettyPrint(String text, boolean lineskip, int whitespace, String color) {
		StringBuilder output = new StringBuilder();
		StringBuilder aux;
		AnsiConsole.systemInstall();
		//newline
		if (lineskip) {
			if (text.indexOf(K.lineSeparator) != 0) {
				output.append(K.lineSeparator);
			}
		}
		if (whitespace > 0 && lineskip) {
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
	
	public static String postProcessElement(Element node, String op, String sort) {
		String result = new String();
		
		if ((sort.equals("KLabel") && !op.equals("'.List`{\",\"`}") || sort.equals("K"))) {
			char firstCh = op.charAt(0);
			if ((firstCh == '#') || (firstCh == '\'')) {
				op = op.substring(1);
			}
			if (op.indexOf("`") != -1) {
				op = op.replaceAll("`", "");
			}
		}
		if (sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("SetItem") || sort.equals("List")) {
			if (op.indexOf("`") != -1) {
				op = op.replaceAll("`", "");
			}
		}
		result = op;
		
		return result;
	}
	
	public void setCmd(CommandLine cmd) {
		this.cmd = cmd;
	}

	public CommandLine getCmd() {
		return cmd;
	}

}