package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class Freezer extends Term {

	private Term term;

	public Freezer(Freezer f) {
		super(f);
		term = f.term;
	}

	public Freezer(Term t) {
		super("KLabel");
		term = t;
	}

	public Term getTerm() {
		return term;
	}

	public void setTerm(Term term) {
		this.term = term;
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
	public Freezer shallowCopy() {
		return new Freezer(this);
	}
}
