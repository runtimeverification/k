package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}
}
