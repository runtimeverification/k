package org.kframework.kil;

import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
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
