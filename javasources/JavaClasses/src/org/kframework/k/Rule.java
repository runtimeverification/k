package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.Constants;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class Rule extends Sentence {
	private String label;

	public Rule(Element element) {
		super(element);
		setLabel(element.getAttribute(Constants.LABEL));
	}

	public Rule(Rule node) {
		super(node);
		this.label = node.getLabel();
	}

	public Rule() {
		super();
	}

	public void setLabel(String label) {
		this.label = label;
	}

	public String getLabel() {
		return label;
	}

	public String toString() {
		String content = "  rule ";

		if (this.label != null && !this.label.equals(""))
			content += "[" + this.label + "]: ";

		content += this.body + " ";

		return content + attributes;
	}

	@Override
	public String toMaude() {

		String sentence = super.toMaude();

		if (this.label != null && !this.label.equals("")) {
			sentence = sentence.replaceFirst("metadata", "label " + label + " metadata");
		}

		return "mb rule " + sentence;
	}

	@Override
	public Element toXml(Document doc) {
		Element rule = doc.createElement(Constants.RULE);
		rule.setTextContent("notImplementedYet");
		return rule;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}
	
	@Override
	public Rule shallowCopy() {
		return new Rule(this);
	}
}
