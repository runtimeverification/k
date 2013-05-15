package org.kframework.kil;

import java.util.ArrayList;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;
import aterm.ATermList;

/**
 * Used for representing parsing ambiguity. Shouldn't exist after disambiguation.
 */
public class Ambiguity extends Collection {

	public Ambiguity(Element element) {
		super(element);
	}

	public Ambiguity(ATermAppl atm) {
		super(atm);

		contents = new ArrayList<Term>();
		ATermList atl = (ATermList) atm.getArgument(0);
		while (!atl.isEmpty()) {
			contents.add((Term) JavaClassesFactory.getTerm(atl.getFirst()));
			atl = atl.getNext();
		}
	}

	public Ambiguity(Ambiguity node) {
		super(node);
	}

	public Ambiguity(String sort, java.util.List<Term> col) {
		super(sort, col);
	}

	@Override
	public String toString() {
		String content = "";

		for (Term term : contents)
			if (term != null)
				content += term + ",";

		if (content.length() > 1)
			content = content.substring(0, content.length() - 1);

		return "amb(" + content + ")";
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
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public Ambiguity shallowCopy() {
		return new Ambiguity(this);
	}

	@Override
	public boolean contains(Object o) {
		if (o instanceof Bracket)
			return contains(((Bracket) o).getContent());
		if (o instanceof Cast)
			return contains(((Cast) o).getContent());
		for (int i = 0; i < contents.size(); i++) {
			if (contents.get(i).contains(o)) {
				return true;
			}
		}
		return false;
	}
}
