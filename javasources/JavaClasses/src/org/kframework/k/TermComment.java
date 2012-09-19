package org.kframework.k;

import org.kframework.exceptions.TransformerException;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Element;


public class TermComment extends Term {

	public TermComment(Element element) {
		super(element);
	}

	public TermComment(TermComment termComment) {
		super(termComment);
	}

	@Override
	public String toMaude() {
		return " (.).Bag ";
	}

	@Override
	public String toString() {
		return "<br />";
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
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public Term shallowCopy() {
		return new TermComment(this);
	}
}
