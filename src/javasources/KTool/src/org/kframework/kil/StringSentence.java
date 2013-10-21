package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
