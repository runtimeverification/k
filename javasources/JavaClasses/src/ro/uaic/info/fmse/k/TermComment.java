package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class TermComment extends Term {

	public TermComment(Element element) {
		super(element);
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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}
}
