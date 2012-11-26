package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class FreezerSubstitution extends Term {

	private String name;
	private String termSort;

	public FreezerSubstitution(FreezerSubstitution f) {
		super(f);
		name = f.name;
		termSort = f.termSort;
	}

	public FreezerSubstitution(String name, String termSort) {
		super("KLabel");
		this.name = name;
		this.termSort = termSort;
	}

	public String getName() {
		return name;
	}

	public void setName(String term) {
		this.name = term;
	}

	public String getTermSort() {
		return termSort;
	}

	public void setTermSort(String term) {
		this.termSort = term;
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
	public FreezerSubstitution shallowCopy() {
		return new FreezerSubstitution(this);
	}
}
