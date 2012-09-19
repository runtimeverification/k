package org.kframework.parser.generator.basic;


import org.kframework.utils.StringUtil;
import org.kframework.utils.Tag;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;


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

	public Rule(Node node) {
		super(node);

		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.value);
		content = StringUtil.unescape(item.getNodeValue());
	}

	public void parse() {
		try {
			String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(content);
			Document doc = XmlLoader.getXMLDoc(parsed);

			Node old = xmlTerm;
			xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
			XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(location, 0), XmlLoader.getLocNumber(location, 1));
			XmlLoader.addFilename(xmlTerm, filename);
			XmlLoader.reportErrors(doc, "rule");

			old.getParentNode().replaceChild(old.getOwnerDocument().importNode(xmlTerm, true), old);

		} catch (Exception e) {
			e.printStackTrace();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse rule: " + e.getLocalizedMessage(), this.filename, location, 0));
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
