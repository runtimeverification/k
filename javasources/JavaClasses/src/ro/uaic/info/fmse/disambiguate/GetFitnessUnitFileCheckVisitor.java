package ro.uaic.info.fmse.disambiguate;

import ro.uaic.info.fmse.k.TermCons;

/**
 * Check to see which branch of an ambiguity has less constructors defined in unrelated files
 * 
 * @author RaduFmse
 * 
 */
public class GetFitnessUnitFileCheckVisitor extends GetFitnessUnitBasicVisitor {

	@Override
	public void visit(TermCons tc) {
		super.visit(tc);

		// TODO: check to see if this constructor should be in this file
		if (true) // if shouldn't be in this file add -1
			score += -1;
	}

	@Override
	public GetFitnessUnitBasicVisitor getInstance() {
		return new GetFitnessUnitFileCheckVisitor();
	}
}
