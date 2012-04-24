package ro.uaic.info.fmse.main;

import java.io.File;
import java.io.IOException;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import ro.uaic.info.fmse.k2m.utils.FileUtil;
import ro.uaic.info.fmse.utils.XMLPrettyPrinter;

public class ConfigurationAbstraction {

	private static CAManager manager;

	public static void main(String[] args) {
		if (args.length >= 1)
			FileUtil.saveInFile("/home/andrei.arusoaie/Desktop/tmp.xml", XMLPrettyPrinter.prettyFormat(applyOnKilFile(args[0])));
	}

	public static Document applyOnKilFile(String KILFile) {
		String absolutePath = new File(KILFile).getAbsolutePath();

		// retrieve the document
		Document doc = getDocument(absolutePath);

		// retrieve the configuration
		NodeList configurations = doc.getElementsByTagName("config");
		if (configurations.getLength() != 1) {
			System.out
					.println("Error: multiple configurations found in the definition (KIL).\n This is not supported yet.\n");
			System.exit(1);
		} else {
			Element config = (Element) configurations.item(0);
			manager = new CAManager(config);
		}

		// retrieve the rules and apply context transformers on it
		NodeList rules = doc.getElementsByTagName("rule");
		for (int i = 0; i < rules.getLength(); i++) {
			rules.item(i).getParentNode().replaceChild(transformRuleElement((Element) rules.item(i)),rules.item(i));
		}

		return doc;
	}

	public static Element transformRuleElement(Element rule) {
		rule = separate(rule);
//		System.out.println("New separated rule: " + XMLPrettyPrinter.prettyFormat(rule));
		return manager.transform(rule);
	}

	private static Element separate(Element rule) {

		// get the body of the rule
		NodeList bodies = rule.getElementsByTagName("body");

		for (int i = 0; i < bodies.getLength(); i++) {
			Element body = (Element) bodies.item(i);

			Element bodyleft = getLHS((Element) body.cloneNode(true));
			Element bodyright = getRHS((Element) body.cloneNode(true));

			// System.out.println(XMLPrettyPrinter.prettyFormat(bodyleft));//
			// .getNodeValue());
			// System.out.println(XMLPrettyPrinter.prettyFormat(bodyright));//
			// .getNodeValue());

			// System.out
			// .println("\n\n\n\n\n\n\n\n\n\n\n\n\n\n=======================\n\n\n\n\n\n\n\n");

			Element newBody = rule.getOwnerDocument().createElement("body");
			Element newRewrite = rule.getOwnerDocument().createElement(
					"rewrite");

			// adding left and right body contents
			Element left = rule.getOwnerDocument().createElement("left");
			NodeList leftChildren = bodyleft.getChildNodes();
			for (int j = 0; j < leftChildren.getLength(); j++)
				if (leftChildren.item(j).getNodeType() == Node.ELEMENT_NODE)
					left.appendChild(leftChildren.item(j));
			
			Element right = rule.getOwnerDocument().createElement("right");
			NodeList rightChildren = bodyright.getChildNodes();
			for (int j = 0; j < rightChildren.getLength(); j++)
				if (rightChildren.item(j).getNodeType() == Node.ELEMENT_NODE)
					right.appendChild(rightChildren.item(j));

			newRewrite.setAttribute("generated", "true");
			left.setAttribute("generated", "true");
			right.setAttribute("generated", "true");
			newRewrite.appendChild(left);
			newRewrite.appendChild(right);
			newBody.appendChild(newRewrite);

			// <rule> is here the parent of <body>
			rule.replaceChild(newBody, body);

		}

		return rule;
	}

	private static Element getLHS(Element cloneNode) {
		return getSide(cloneNode, "left");
	}

	private static Element getRHS(Element cloneNode) {
		return getSide(cloneNode, "right");
	}

	private static Element getSide(Element cloneNode, String side) {

		if (!cloneNode.getNodeName().equals("rewrite")) {

			NodeList contents = cloneNode.getChildNodes();
			for (int i = 0; i < contents.getLength(); i++) {

				if (contents.item(i).getNodeType() == Node.ELEMENT_NODE) {

					Element content = (Element) contents.item(i);

					if (content.getNodeName().equals("rewrite")) {
						// in a rewrite: term goes up, replacing <rewrite>
						// <rewrite>
						// <left>
						// <term>
						// <right>

						// this assumes that a rewrite contains only one element
						// node <left>/<right>
						Element sideElement = (Element) ((Element) contents
								.item(i)).getElementsByTagName(side).item(0);

						// remove rewrite element
						cloneNode.removeChild(content);

						NodeList leftcontent = sideElement.getChildNodes();

						for (int j = 0; j < leftcontent.getLength(); j++)
							if (leftcontent.item(j).getNodeType() == Node.ELEMENT_NODE) {
								cloneNode.appendChild((Element) leftcontent
										.item(j));
							}
					} else {
						if (content.getNodeType() == Node.ELEMENT_NODE)
							cloneNode.replaceChild(
									getSide((Element) content, side), content);
					}
				}
			}
		}

		return cloneNode;
	}

	public static Document getDocument(String file) {
		try {
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder dBuilder;
			dBuilder = dbFactory.newDocumentBuilder();
			Document doc = dBuilder.parse(file);
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
}
