package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * Represents a <br />
 * occurring for formatting in a bag of cells
 */
public class TermComment extends Term {

	public TermComment(Element element) {
		super(element);
	}

	public TermComment(TermComment termComment) {
		super(termComment);
	}

	public TermComment(ATermAppl element) {
		super(element);
	}

	@Override
	public String toString() {
		return "<br />";
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
	public Term shallowCopy() {
		return new TermComment(this);
	}

	@Override
	public int hashCode() {
		return 53;
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof TermComment))
			return false;
		return true;
	}
}
