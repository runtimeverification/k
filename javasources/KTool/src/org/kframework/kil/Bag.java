package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import java.util.Collections;
import java.util.List;

/** A bag. Contents should be a Cell or BagItem node, or term of sort Bag or BagItem */
public class Bag extends Collection {

	public static final Bag EMPTY = new Bag(Collections.<Term> emptyList());

	public Bag(String location, String filename) {
		super(location, filename, "Bag");
	}

	public Bag(Element element) {
		super(element);
	}

	public Bag(ATermAppl atm) {
		super(atm);
	}

	public Bag(Bag node) {
		super(node);
	}

	public Bag() {
		super("Bag");
	}

	public Bag(List<Term> col) {
		super("Bag", col);
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
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public Bag shallowCopy() {
		return new Bag(this);
	}
}
