package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

/**
 * A rule declaration.
 * The left and right hand sides of the rewrite are described by the single term
 * {@code body} which allows {@link Rewrite} nodes to describe the changes.
 * Any explicit attributes on the rule are stored in {@link #attributes}.
 */
public class Rule extends Sentence {
	/** Label from {@code rule[}label{@code ]:} syntax or "". Currently unrelated to attributes */
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

	public Rule(Term lhs, Term rhs) {
		super();
		this.setBody(new Rewrite(lhs, rhs));
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
