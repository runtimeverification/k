package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;

public class BestFitFilter extends BasicTransformer {

	public BestFitFilter(GetFitnessUnitBasicVisitor gfubv, Context context) {
		super("Best fit filter", context);
		getFitnessUnit = gfubv;
	}

	private GetFitnessUnitBasicVisitor getFitnessUnit;

	public ASTNode transform(Ambiguity amb) throws TransformerException {
		amb = (Ambiguity) super.transform(amb);

		int maximum = getFitnessUnit(amb.getContents().get(0));

		// choose the maximums from the list of ambiguities
		java.util.List<Term> terms = new ArrayList<Term>();
		for (Term trm1 : amb.getContents()) {
			int temp = getFitnessUnit(trm1);
			if (temp > maximum)
				maximum = temp;
		}

		for (Term trm1 : amb.getContents()) {
			if (getFitnessUnit(trm1) == maximum)
				terms.add(trm1);
		}

		if (terms.size() == 1)
			return terms.get(0);
		else
			amb.setContents(terms);

		return amb;
	}

	private int getFitnessUnit(Term t) {
		GetFitnessUnitBasicVisitor fitnessVisitor = getFitnessUnit.getInstance();
		t.accept(fitnessVisitor);
		return fitnessVisitor.getScore();
	}
}
