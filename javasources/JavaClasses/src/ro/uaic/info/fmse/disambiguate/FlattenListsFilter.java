package ro.uaic.info.fmse.disambiguate;

import java.util.ArrayList;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Collection;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class FlattenListsFilter extends BasicTransformer {

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
