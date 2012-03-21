package k3.basic;

import k.utils.Error;
import k.utils.StringUtil;
import k.utils.Tag;
import k.utils.XmlLoader;

import org.w3c.dom.*;

public class Rule extends Sentence {
	private String content;

	public Rule clone() {
		// super.clone();
		//
		// Rule r = new Rule();
		// r.content = content;
		// r.copy(this);

		return this;
	}

	public Rule() {
	}

	public Rule(Node node, String filename) {
		this.filename = filename;

		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.location);
		location = item.getNodeValue();
		xmlTerm = node;

		item = attr.getNamedItem(Tag.value);
		content = StringUtil.unescape(item.getNodeValue());
	}

	public void parse() {
		try {
			String parsed = k3parser.KParser.ParseKRuleString(content);
			Document doc = XmlLoader.getXMLDoc(parsed);

			Node old = xmlTerm;
			xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
			XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(location, 0), XmlLoader.getLocNumber(location, 1), filename);
			XmlLoader.reportErrors(xmlTerm);

			old.getParentNode().replaceChild(old.getOwnerDocument().importNode(xmlTerm, true), old);

		} catch (Exception e) {
			e.printStackTrace();
			Error.report("Cannot parse rule: " + e.getLocalizedMessage());
		}
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}

	@Override
	public SentenceType getType() {
		return SentenceType.RULE;
	}
}
