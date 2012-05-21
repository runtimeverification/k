package k3.basic;

import k.utils.StringUtil;
import k.utils.Tag;

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
