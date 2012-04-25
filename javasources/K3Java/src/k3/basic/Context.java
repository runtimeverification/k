package k3.basic;

import k.utils.Error;
import k.utils.StringUtil;
import k.utils.Tag;
import k.utils.XmlLoader;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class Context extends Sentence {
	private static final long serialVersionUID = 1L;
	private String content;

	public Context clone() {
		return this;
	}
	
	public Context() {
	}

	public Context(Node node, String filename) {
		this.filename = filename;

		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.location);
		location = item.getNodeValue();
		xmlTerm = node;

		item = attr.getNamedItem(Tag.value);
		setContent(StringUtil.unescape(item.getNodeValue()));
	}

	public void parse() {
		try {
			String parsed = k3parser.KParser.ParseKRuleString(content);
			Document doc = XmlLoader.getXMLDoc(parsed);

			Node old = xmlTerm;
			xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
			XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(location, 0), XmlLoader.getLocNumber(location, 1));
			XmlLoader.addFilename(xmlTerm, filename);
			XmlLoader.reportErrors(doc);

			old.getParentNode().replaceChild(old.getOwnerDocument().importNode(xmlTerm, true), old);

		} catch (Exception e) {
			e.printStackTrace();
			Error.report("Cannot parse context: " + e.getLocalizedMessage());
		}
	}

	@Override
	public SentenceType getType() {
		return SentenceType.CONTEXT;
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}
}
