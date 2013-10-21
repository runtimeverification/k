package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import java.util.Collections;


/** An associative list of terms of sort List or ListItem */
public class List extends Collection {

    public static final List EMPTY = new List(Collections.<Term>emptyList());

	public List(Element element) {
		super(element);
	}

	public List(ATermAppl atm) {
		super(atm);
	}

	public List(List node) {
		super(node);
	}

	public List(String location, String filename) {
		super(location, filename, "List");
	}

	public List() {
		super("List");
	}

	public List(java.util.List<Term> col) {
		super("List", col);
	}

	@Override
	public String toString() {
		return super.toString();
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
	public List shallowCopy() {
		return new List(this);
	}
}
