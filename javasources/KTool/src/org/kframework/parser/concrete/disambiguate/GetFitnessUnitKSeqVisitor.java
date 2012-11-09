package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.KSequence;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;

/**
 * Check to see which branch of an ambiguity has less K insertions
 * 
 * @author RaduFmse
 * 
 */
public class GetFitnessUnitKSeqVisitor extends GetFitnessUnitBasicVisitor {

	@Override
	public void visit(TermCons tc) {
		super.visit(tc);

		for (Term t : tc.getContents()) {
			if (t instanceof KSequence)
				score -= 1;
		}
	}

	@Override
	public GetFitnessUnitBasicVisitor getInstance() {
		return new GetFitnessUnitKSeqVisitor();
	}
}
