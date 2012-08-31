package ro.uaic.info.fmse.k;

import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class KInjectedLabel extends Term {

	private Term term;

	public KInjectedLabel(String location, String filename) {
		super(location, filename, "KLabel");
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
		return "#_(" + term + ")";
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
