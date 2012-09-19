package org.kframework.disambiguate;

import java.util.ArrayList;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Term;
import org.kframework.visitors.BasicTransformer;


public class AmbDuplicateFilter extends BasicTransformer {
	public AmbDuplicateFilter() {
		super("Remove ambiguity duplicates");
		// TODO Auto-generated constructor stub
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {

		// remove duplicate ambiguities
		// should be applied after updating something like variable declarations
		java.util.List<Term> children = new ArrayList<Term>();
		for (Term t1 : amb.getContents()) {
			boolean unique = true;
			for (Term t2 : children)
				if (t1 != t2 && t1.equals(t2))
					unique = false;
			if (unique)
				children.add(t1);
		}

		if (children.size() > 1) {
			amb.setContents(children);
			return super.transform(amb);
		} else
			return super.transform(children.get(0));
	}
}
