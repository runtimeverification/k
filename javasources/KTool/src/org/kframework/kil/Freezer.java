package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** A frozen term. Contains a {@link FreezerHole}. */
public class Freezer extends Term {

	private Term term;

	public Freezer(Freezer f) {
		super(f);
		term = f.term;
	}

	public Freezer(Term t) {
		super("K");
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

  @Override
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

	@Override
	public Freezer shallowCopy() {
		return new Freezer(this);
	}

	@Override
	public String toString() {
		return "#freezer " + term.toString() + "(.KList)";
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Freezer)) return false;
		Freezer f = (Freezer)o;
		return term.equals(f.term);
	}

	@Override
	public boolean contains(Object o) {
		if (o instanceof Bracket)
			return contains(((Bracket)o).getContent());
		if (o instanceof Cast)
			return contains(((Cast)o).getContent());
		if (!(o instanceof Freezer)) return false;
		Freezer f = (Freezer)o;
		return term.contains(f.term);
	}


	@Override
	public int hashCode() {
		return term.hashCode();
	}
}
