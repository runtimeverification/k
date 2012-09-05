package ro.uaic.info.fmse.disambiguate;

import java.util.ArrayList;
import java.util.List;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.KSequence;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class CorrectKSeqFilter extends BasicTransformer {

	public ASTNode transform(Ambiguity amb) {
		List<Term> children = new ArrayList<Term>();
		for (Term t : amb.getContents()) {
			if (t instanceof KSequence) {
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
