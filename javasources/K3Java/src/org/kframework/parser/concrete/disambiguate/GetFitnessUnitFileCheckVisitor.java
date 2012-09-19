package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;

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

		String localFile = tc.getFilename();
		String consFile = tc.getProduction().getFilename();
		if (!DefinitionHelper.isRequiredEq(consFile, localFile)) {// if shouldn't be in this file add -1
			score += -1;
			// System.out.println("TC: " + tc.getCons() + " in file: " + localFile);
		}
	}

	@Override
	public GetFitnessUnitBasicVisitor getInstance() {
		return new GetFitnessUnitFileCheckVisitor();
	}
}
