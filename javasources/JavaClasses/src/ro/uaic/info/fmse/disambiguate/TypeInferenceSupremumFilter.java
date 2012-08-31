package ro.uaic.info.fmse.disambiguate;

import java.util.ArrayList;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class TypeInferenceSupremumFilter extends BasicTransformer {

	public ASTNode transform(Ambiguity amb) {

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
