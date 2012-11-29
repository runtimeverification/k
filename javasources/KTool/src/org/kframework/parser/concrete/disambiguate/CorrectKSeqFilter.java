package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KSequence;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.List;

public class CorrectKSeqFilter extends BasicTransformer {

	public CorrectKSeqFilter() {
		super("Correct K sequences");
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {
		List<Term> children = new ArrayList<Term>();
		for (Term t : amb.getContents()) {
			if (t instanceof KSequence) {
				children.add(t);
			}
		}

		if (children.size() == 0 || children.size() == amb.getContents().size())
			return super.transform(amb);
		if (children.size() == 1)
			return children.get(0).accept(this);
		amb.setContents(children);
		return super.transform(amb);
	}
}
