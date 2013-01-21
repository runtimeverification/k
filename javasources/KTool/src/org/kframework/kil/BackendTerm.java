package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** An uninterpreted string,
 * used to represent (subterms of) Maude which 
 * can't be parsed into valid terms.
 */
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
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

	@Override
	public BackendTerm shallowCopy() {
		return new BackendTerm(this);
	}
}
