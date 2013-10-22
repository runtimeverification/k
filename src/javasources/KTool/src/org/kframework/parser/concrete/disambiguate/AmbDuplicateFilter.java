package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;

public class AmbDuplicateFilter extends BasicTransformer {
	public AmbDuplicateFilter(Context context) {
		super("Remove ambiguity duplicates", context);
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
