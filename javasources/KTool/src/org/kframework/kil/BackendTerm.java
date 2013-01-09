package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class BackendTerm extends Term {

	public BackendTerm(BackendTerm term) {
		super(term);
		this.value = term.value;
	}

	String value;

	public BackendTerm(String sort, String value) {
		super(sort);
		this.value = value;
	}

	public String toString() {
		return this.value;
	}

	public String getValue() {
		return value;
	}

	public void setValue(String value) {
		this.value = value;
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
	public BackendTerm shallowCopy() {
		return new BackendTerm(this);
	}
}
