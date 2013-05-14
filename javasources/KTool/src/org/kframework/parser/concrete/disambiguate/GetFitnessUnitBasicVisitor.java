package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;

public abstract class GetFitnessUnitBasicVisitor extends BasicVisitor {
	public GetFitnessUnitBasicVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}

	protected int score = 0;

	public int getScore() {
		return score;
	}

	public void setScore(int score) {
		this.score = score;
	}

	public abstract GetFitnessUnitBasicVisitor getInstance();
}
