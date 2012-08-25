package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.apache.commons.cli.CommandLine;
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
/*	public String getResultTagAttr(File file, String attrName) {
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
	}*/

	/* return the value for the attribute attrName of search-result tag */
	/*public String getSearchTagAttr(File file, String attrName) {
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
	}*/

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
	
	public static String printSearchResults(Element elem) {
		String result = "";
		String solutionNumber = elem.getAttribute("solution-number");
		String stateNumber = elem.getAttribute("state-number");
		if (!solutionNumber.equals("NONE")) {
			result += K.lineSeparator + (PrettyPrintOutput.ANSI_BLUE + "Solution " + solutionNumber + ", state " + stateNumber + ":" + PrettyPrintOutput.ANSI_NORMAL);
		}
		return result;
	}
	
	public static String printStatistics(Element elem) {
		String result = "";
		if ("search".equals(K.maude_cmd)) {
			String totalStates = elem.getAttribute("total-states");
			String totalRewrites = elem.getAttribute("total-rewrites");
			String realTime = elem.getAttribute("real-time-ms");
			String cpuTime = elem.getAttribute("cpu-time-ms");
			String rewritesPerSecond = elem.getAttribute("rewrites-per-second");
			result += PrettyPrintOutput.ANSI_BLUE + "states: " + totalStates + " rewrites: " + totalRewrites + " in " + cpuTime + "ms cpu (" + realTime + "ms real) (" + rewritesPerSecond + " rewrites/second)" + PrettyPrintOutput.ANSI_NORMAL;
		} else if ("erewrite".equals(K.maude_cmd)){
			String totalRewrites = elem.getAttribute("total-rewrites");
			String realTime = elem.getAttribute("real-time-ms");
			String cpuTime = elem.getAttribute("cpu-time-ms");
			String rewritesPerSecond = elem.getAttribute("rewrites-per-second");
			result += PrettyPrintOutput.ANSI_BLUE + "rewrites: " + totalRewrites + " in " + cpuTime + "ms cpu (" + realTime + "ms real) (" + rewritesPerSecond + " rewrites/second)" + PrettyPrintOutput.ANSI_NORMAL;
		}
		return result;
	}


	public List<String> processDoc(String fileName) {
		File input = new File(fileName);
		Document doc = XmlUtil.readXML(input);
		NodeList list = null;
		Node nod = null;
		List<String> result = new LinkedList<String>();

		if (K.maude_cmd.equals("erewrite")) {
			list = doc.getElementsByTagName("result");
			nod = list.item(0);
			if (nod == null) {
				Error.report("Pretty Print Output: The node with result tag wasn't found");
			} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
				Element elem = (Element) nod;
				NodeList child = elem.getChildNodes();
				for (int i = 0; i < child.getLength(); i++) {
					if (child.item(i).getNodeType() == Node.ELEMENT_NODE) {
						result.add(print((Element) child.item(i), false, 0, ANSI_NORMAL));
					}
				}
				if (K.statistics) {
					result.add(printStatistics(elem));
				}
			}
		} else if (K.maude_cmd.equals("search")) {
			list = doc.getElementsByTagName("search-result");
			for (int i = 0; i < list.getLength(); i++) {
				nod = list.item(i);
				if (nod == null) {
					Error.report("Pretty Print Output: The node with search-result tag wasn't found");
				} else if (nod != null && nod.getNodeType() == Node.ELEMENT_NODE) {
					Element elem = (Element) nod;
					if (elem.getAttribute("solution-number").equals("NONE")) {
						if (i == 0) result.add("Found no solution");
						continue;
//						String output = FileUtil.getFileContent(K.maude_out);
//						Error.report("Unable to parse Maude's search results:\n" + output);
					}
					// using XPath for direct access to the desired node
					XPathFactory factory2 = XPathFactory.newInstance();
					XPath xpath2 = factory2.newXPath();
					String s2 = "substitution/assignment[last()]/term[2]";
					Object result2;
					try {
						result2 = xpath2.evaluate(s2, nod, XPathConstants.NODESET);
						if (result2 != null) {
							NodeList nodes2 = (NodeList) result2;
							nod = nodes2.item(0);
							result.add(printSearchResults(elem) + K.lineSeparator + print((Element) nod, false, 0, ANSI_NORMAL));
							if (K.statistics) {
								result.add(printStatistics(elem));
							}
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

	private static String print(Element node, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		String op = node.getAttribute("op");
		String sort = node.getAttribute("sort");
		ArrayList<Element> list = XmlUtil.getChildElements(node);

		if (sort.equals("BagItem") && op.equals("<_>_</_>")
				|| sort.equals("[Bag]") && op.equals("<_>_</_>")) {
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
		if (sort.equals("BagItem") && !op.equals("<_>_</_>")
				|| sort.equals("[Bag]") && !op.equals("<_>_</_>")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace + indent, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace + indent, ANSI_NORMAL);
				//System.out.println("the content of the bag is:" + sb);
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
			int m = Utils.countUnderscores(op);

			//postprocess
			op = postProcessElement(node, op, sort);

			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				//like in the case of an associative operator (<term op="_~>_" sort="K">); "_~>_" is an associative operator
				if (op.equals("_~>_")) {
					sb = lessUnderscoresAssocCase(list, op, false, whitespace, ANSI_NORMAL);
				}
				else {
					sb = lessUnderscoresCase(list, op, n, m, false, whitespace, ANSI_NORMAL);
				}
			}
			//like in the case of <term op="var`{K`}`(_`)" sort="K"> (equal number of underscores and children)
			else if (m == n) {
				sb = generalCase(list, op, false, whitespace, ANSI_NORMAL, true);
			}
			return sb.toString();
		}
		if (sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("SetItem")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//postprocess
			op = postProcessElement(node, op, sort);

			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace, ANSI_NORMAL);
			}
			else {
				sb = generalCase(list, op, false, whitespace, ANSI_NORMAL, false);
			}
			return sb.toString();
		}
		if (sort.equals("NeBag") || sort.equals("NeMap") || sort.equals("NeList") || sort.equals("NeSet")) {
			sb = new StringBuilder();
			List<String> elements = new ArrayList<String>();
			StringBuilder sb_ = new StringBuilder();
			for (int i = 0; i < list.size(); i++) {
				Element child = list.get(i);
				if (sort.equals("NeMap") || sort.equals("NeList") || sort.equals("NeSet")) {
					elements.add(prettyPrint(print(child, true, whitespace + indent, ANSI_NORMAL), true, whitespace + indent, ANSI_NORMAL));
				}
				else {
					elements.add(prettyPrint(print(child, false, whitespace + indent, ANSI_NORMAL), false, whitespace + indent, ANSI_NORMAL));
				}
			}
			for (String s : elements) {
				sb_.append(s);
				if (sort.equals("NeBag")) {
					sb_.append(" "); //for pretty-printing
				}
			}
			sb.append(sb_);	
			return sb.toString();
		}
		if (sort.equals("List") || sort.equals("Set") || sort.equals("Bag") || sort.equals("Map")
				//we may find this sorts in intermediate configurations of the stepper
				|| sort.equals("[List]") || sort.equals("[Set]") || sort.equals("[Map]") ) {
			sb = new StringBuilder();
			//postprocess
			op = postProcessElement(node, op, sort);

			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//"__" is an associative operator
			if (op.equals("__")) {
				sb = lessUnderscoresAssocCase(list, op, false, whitespace, ANSI_NORMAL);
			}
			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace + indent, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace + indent, ANSI_NORMAL);
			}
			else {
				sb = generalCase(list, op, false, whitespace, ANSI_NORMAL, true);
			}
			return sb.toString();
		}
		if ((sort.equals("KLabel") && !op.equals("'.List`{\",\"`}") )
				|| sort.equals("[KLabel]") && !op.equals("'.List`{\",\"`}")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//postprocess
			op = postProcessElement(node, op, sort);

			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace + indent, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace + indent, ANSI_NORMAL);
			}
			else {
				sb = generalCase(list, op, false, whitespace + indent, ANSI_NORMAL, true);
			}
			return sb.toString();
		}
		if (sort.equals("KLabel") && op.equals("'.List`{\",\"`}")
				|| sort.equals("[KLabel]") && op.equals("'.List`{\",\"`}")) {
			sb = new StringBuilder();
			//Element previous = XmlUtil.getPreviousSiblingElement(node);
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
		//this is the case of builtins
		if (sort.startsWith("#") || sort.startsWith("[#")) {
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//#Id is treated separately
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
			else if (sort.equals("#NzNat") && op.equals("sNat_")) {
				sb = new StringBuilder();
				sb.append(node.getAttribute("number"));
				return sb.toString();
			}
			//like the case of #Zero, #Bool, #Char and #String sorts
			else if ((m == 0) && (n == 0) ||
					(sort.equals("#Zero") || sort.equals("#Bool") || sort.equals("#Char") || sort.equals("#String"))) {
				sb = new StringBuilder();
				sb.append(op);
				return sb.toString();
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace, ANSI_NORMAL);
			}
			else {
				sb = generalCase(list, op, false, whitespace, ANSI_NORMAL, true);
			}
			return sb.toString();
		}
		if (op.equals(".")) {
			sb = new StringBuilder();
			sb.append(".");
			return sb.toString();
		}
		if (sort.equals("List`{K`}") && op.equals(".List`{K`}") 
				|| sort.equals("[List`{K`}]") && op.equals("[.List`{K`}]")) {
			return "";
		}
		if (sort.equals("List`{K`}") && !op.equals(".List`{K`}") 
				|| sort.equals("[List`{K`}]") && !op.equals("[.List`{K`}]")) {
			sb = new StringBuilder();
			//n = nr of child nodes
			int n = list.size();
			// m = nr of "_" characters from op atrribute
			int m = Utils.countUnderscores(op);

			//postprocess
			op = postProcessElement(node, op, sort);

			//HOLE case
			if (m == 0 && n == 0) {
				sb.append(op);
			}
			//freezer case
			else if (m == 0 && n > 0) {
				sb = freezerCase(list, op, n, false, whitespace + indent, ANSI_NORMAL);
			}
			else if (m < n && n > 0 && m > 0) {
				sb = lessUnderscoresCase(list, op, n, m, false, whitespace + indent, ANSI_NORMAL);
			}
			else {
				sb = generalCase(list, op, false, whitespace + indent, ANSI_NORMAL, true);
			}
			return sb.toString();
		}
		/*else {
			return "rule no implemented yet: op=" + op + " sort=" + sort;
		}*/
		return sb.toString();
	}

	private static String prettyPrint(String text, boolean lineskip, int whitespace, String color) {
		StringBuilder output = new StringBuilder();
		StringBuilder aux;

		//newline
		if (lineskip) {
			// if the text doesn't start with a line separator for writing on a new line, add one
			if (! text.startsWith(K.lineSeparator)) {
				output.append(K.lineSeparator);
			}
		}
		if (whitespace > 0 && lineskip) {
			String space = Utils.buildWhitespace(whitespace);
			output.append(space);
		}
		if (K.color) {
			if (!color.equals(ANSI_NORMAL)) {
				output.append(color);
				output.append(text);
				output.append(ANSI_NORMAL);
			}
			else if (text.indexOf("|->") != -1) {
				aux = new StringBuilder();
				aux = Utils.colorSymbol(text, "|->", ANSI_PURPLE);
				output.append(aux);
			}
			else if (text.indexOf("~>") != -1) {
				aux = new StringBuilder();
				aux = Utils.colorSymbol(text, "~>", ANSI_BLUE);
				output.append(aux);
			}
			else {
				output.append(text);
			}
		}
		else {
			output.append(text);
		}

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
		if (sort.equals("MapItem") || sort.equals("ListItem") || sort.equals("SetItem") 
				|| sort.equals("List") || sort.equals("Set") || sort.equals("Bag") || sort.equals("Map")) {
			if (op.indexOf("`") != -1) {
				op = op.replaceAll("`", "");
			}
		}
		result = op;

		return result;
	}

	//when the number of underscores = 0 and the number of children > 0 
	public static StringBuilder freezerCase(List<Element> list, String op, int n, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		List<String> elements = new ArrayList<String>();

		for (int i = 0; i < n; i++) {
			Element child = list.get(i);
			String prettyStr = prettyPrint(print(child, lineskip, whitespace, color), lineskip, whitespace, color);
			if (prettyStr.length() > 0) {
				elements.add(prettyStr.trim());
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

		return sb;
	}

	//when the number of underscores is less than the number of children
	public static StringBuilder lessUnderscoresCase(List<Element> list, String op, int n, int m, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		List<String> elements = new ArrayList<String>();

		for (int i = 0; i < list.size(); i++) {
			Element child = list.get(i);
			String elem = prettyPrint(print(child, lineskip, whitespace, color), lineskip, whitespace, color);
			elements.add(elem);
		}
		StringBuilder sb_ = new StringBuilder(op);
		sb_ = Utils.insertSpaceNearUnderscores(op);
		op = sb_.toString();
		StringBuilder sb1 = Utils.replaceAllUnderscores(op, elements);
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

		return sb;
	}

	//when the number of underscores is less than the number of children and the operator is associative
	public static StringBuilder lessUnderscoresAssocCase(List<Element> list, String op, boolean lineskip, int whitespace, String color) {
		StringBuilder sb = new StringBuilder();
		List<String> elements = new ArrayList<String>();

		StringBuilder aux = new StringBuilder();
		for (int i = 0; i < list.size(); i++) {
			Element child = list.get(i);
			String elem = prettyPrint(print(child, lineskip, whitespace, color), lineskip, whitespace, color);
			elements.add(elem);
		}
		aux = Utils.replaceAllUnderscoresAssoc(op, elements);
		sb.append(aux);

		return sb;
	}

	//when the number of underscores is equal with the number of children
	public static StringBuilder generalCase(List<Element> list, String op, boolean lineskip, int whitespace, String color, boolean addParens) {
		StringBuilder sb = new StringBuilder();
		List<String> elements = new ArrayList<String>();

		for (int i = 0; i < list.size(); i++) {
			Element child = list.get(i);
			String elem = prettyPrint(print(child, lineskip, whitespace, color), lineskip, whitespace, color);
			elements.add(elem.trim());
		}
		if (op.indexOf("`") != -1) {
			op = op.replaceAll("`", "");
		}
		char firstCh = op.charAt(0);
		if (firstCh == '\'') {
			op = op.substring(1);
		}
		StringBuilder sb_ = new StringBuilder(op);
		if (K.parens && addParens) {
			sb_ = Utils.insertParenthesisNearUnderscores(list, op);
		}
		op = sb_.toString();
		if (! K.parens || ! addParens) {
			sb_ = Utils.insertSpaceNearUnderscores(op);
		}
		op = sb_.toString();
		
		StringBuilder sb1 = new StringBuilder(op);
		//replace each "_" with its children representation
		sb1 = Utils.replaceAllUnderscores(op, elements);
		op = sb1.toString();
		sb.append(op);
		return sb;
	}

	public void setCmd(CommandLine cmd) {
		this.cmd = cmd;
	}

	public CommandLine getCmd() {
		return cmd;
	}

}