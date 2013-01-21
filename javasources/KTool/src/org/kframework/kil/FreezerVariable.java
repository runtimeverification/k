package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** Unused */
public class FreezerVariable extends Term {

	private String name;

	public FreezerVariable(FreezerVariable f) {
		super(f);
		name = f.name;
	}

	public FreezerVariable(String sort, String name) {
		super(sort);
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setName(String term) {
		this.name = term;
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
	public FreezerVariable shallowCopy() {
		return new FreezerVariable(this);
	}
}
