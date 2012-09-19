package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Collection;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class FlattenListsFilter extends BasicTransformer {

	public FlattenListsFilter() {
		super("Flatten lists");
	}

	public ASTNode transform(Collection c) throws TransformerException {
		boolean found;
		do {
			found = false;
			java.util.List<Term> contents = new ArrayList<Term>();
			for (Term t : c.getContents()) {
				if (t.getClass() == c.getClass()) {
					found = true;
					Collection c2 = (Collection) t;
					contents.addAll(c2.getContents());
				} else
					contents.add(t);
			}
			c.setContents(contents);
		} while (found);

		return super.transform(c);
	}
}
