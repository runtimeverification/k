package org.kframework.disambiguate;

import java.util.ArrayList;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Term;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.BasicTransformer;


public class TypeInferenceSupremumFilter extends BasicTransformer {

	public TypeInferenceSupremumFilter() {
		super("Type inference supremum");
		// TODO Auto-generated constructor stub
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {

		// choose the maximum from the list of ambiguities
		java.util.List<Term> terms = new ArrayList<Term>();
		for (Term trm1 : amb.getContents()) {
			boolean topSort = true;
			for (Term trm2 : amb.getContents()) {
				if (DefinitionHelper.isSubsorted(trm2.getSort(), trm1.getSort())) {
					topSort = false;
					break;
				}
			}
			if (topSort)
				terms.add(trm1);
		}

		if (terms.size() == 1)
			return terms.get(0).accept(this);
		else
			amb.setContents(terms);

		return super.transform(amb);
	}
}
