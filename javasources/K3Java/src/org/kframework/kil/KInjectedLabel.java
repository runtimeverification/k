package org.kframework.kil;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class KInjectedLabel extends Term {

	private Term term;

	public KInjectedLabel(String location, String filename) {
		super(location, filename, "KLabel");
	}

	public KInjectedLabel(KInjectedLabel l) {
		super(l);
		term = l.term;
	}
	
	public KInjectedLabel(Term t) {
		super("KLabel");
		term = t;
	}

	public Term getTerm() {
		return term;
	}

	public void setTerm(Term term) {
		this.term = term;
	}

	public String toString() {
		return "# " + term;
	}

	@Override
	public String toMaude() {
		if (MetaK.isKSort(term.getSort())) {
			return term.getSort() + "2KLabel_(" + term.toMaude() + ")";
		}
		return "#_(" + term.toMaude() + ")";
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
	public KInjectedLabel shallowCopy() {
		return new KInjectedLabel(this);
	}
}
