package org.kframework.kil;

import java.util.Collections;
import java.util.List;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/** Set contents have sort Set or SetItem */
public class Set extends Collection {

	public static final Set EMPTY = new Set(Collections.<Term> emptyList());

	public Set(Element element) {
		super(element);
	}

	public Set(ATermAppl atm) {
		super(atm);
	}

	public Set(Set node) {
		super(node);
	}

	public Set(String location, String filename) {
		super(location, filename, "Set");
	}

	public Set(List<Term> col) {
		super("Set", col);
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
	public Set shallowCopy() {
		return new Set(this);
	}
}
