package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

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
