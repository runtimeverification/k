package org.kframework.parser.generator.basic;


import org.kframework.utils.StringUtil;
import org.kframework.utils.Tag;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class Comment extends Sentence {
	private String content;

	public Comment clone() {
		return this;
	}

	public Comment() {
	}

	public Comment(Node node) {
		super(node);

		NamedNodeMap attr = node.getAttributes();
		Element elm = node.getOwnerDocument().createElement("moduleComment");
		NamedNodeMap nmp = node.getAttributes();
		for (int i = 0; i < nmp.getLength(); i++)
			elm.setAttribute(nmp.item(i).getNodeName(), nmp.item(i).getNodeValue());
		xmlTerm = elm;

		Node item = attr.getNamedItem(Tag.value);
		content = StringUtil.unescape(item.getNodeValue());
		if (content.startsWith("//"))
			content = content.substring(2, content.length() - 1); // remove // and \n from begining and end
		else
			content = content.substring(2, content.length() - 2); // remove /* and */ from begining and end

		if (content.startsWith("@")) {
			elm.setAttribute("special", "latex");
			content = content.substring(1);
		}
		if (content.startsWith("!")) {
			elm.setAttribute("special", "preamble");
			content = content.substring(1);
		}

		elm.setAttribute(Tag.value, content);
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}

	@Override
	public SentenceType getType() {
		return SentenceType.COMMENT;
	}
}
