package k3.basic;

import k.utils.StringUtil;
import k.utils.Tag;

import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;

public class CommentDef extends ModuleItem {
	private String content;

	public CommentDef clone() {
		return this;
	}

//	public CommentDef() {
//	}

	public CommentDef(Node node) {
		super(node);

		NamedNodeMap attr = node.getAttributes();
		Element elm = node.getOwnerDocument().createElement("defComment");
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
	public ModuleType getType() {
		return ModuleType.COMMENT;
	}
}
