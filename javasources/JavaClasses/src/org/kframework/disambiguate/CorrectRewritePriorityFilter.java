package org.kframework.disambiguate;

import java.util.ArrayList;
import java.util.List;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Rewrite;
import org.kframework.k.Term;
import org.kframework.visitors.BasicTransformer;


public class CorrectRewritePriorityFilter extends BasicTransformer {

	public CorrectRewritePriorityFilter() {
		super("Correct Rewrite priority");
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {
		List<Term> children = new ArrayList<Term>();
		for (Term t : amb.getContents()) {
			if (t instanceof Rewrite) {
				children.add(t);
			}
		}

		if (children.size() == 0 || children.size() == amb.getContents().size())
			return super.transform(amb);
		if (children.size() == 1)
			return super.transform(children.get(0));
		amb.setContents(children);
		return super.transform(amb);
	}
}
