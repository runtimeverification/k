package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

/**
 * Used as a container for unparsed sentences like rule, context and configuration.
 * 
 * @author Radu
 * 
 */
public class StringSentence extends ModuleItem {
	private String content;
	private String label;
	private String type;

	public StringSentence(String content, String type, String label) {
		this.content = content;
		this.type = type;
		this.label = label;
	}

	public StringSentence(Element element) {
		super(element);
		content = StringUtil.unescape(element.getAttribute(Constants.VALUE_value_ATTR));
		label = element.getAttribute(Constants.LABEL_label_ATTR);
		type = element.getNodeName();
		java.util.List<Element> its = XML.getChildrenElementsByTagName(element, Constants.ATTRIBUTES);
		// assumption: <attributes> appears only once
		if (its.size() > 0) {
			attributes.setAll((Attributes) JavaClassesFactory.getTerm(its.get(0)));
		} else {
			if (attributes == null)
				attributes = new Attributes();
			attributes.addAttribute("generated", "generated");
		}
	}

	public StringSentence(StringSentence node) {
		super(node);
		this.content = node.content;
	}

	public String toString() {
		return type+"["+label+"]:"+content;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}

	@Override
	public StringSentence shallowCopy() {
		return new StringSentence(this);
	}

	public void setType(String type) {
		this.type = type;
	}

	public String getType() {
		return type;
	}

	public String getLabel() {
		return label;
	}

	public void setLabel(String label) {
		this.label = label;
	}
}
