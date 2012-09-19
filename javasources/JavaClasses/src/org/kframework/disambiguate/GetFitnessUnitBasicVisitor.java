package org.kframework.disambiguate;

import org.kframework.visitors.BasicVisitor;

public abstract class GetFitnessUnitBasicVisitor extends BasicVisitor {
	protected int score = 0;

	public int getScore() {
		return score;
	}

	public void setScore(int score) {
		this.score = score;
	}

	public abstract GetFitnessUnitBasicVisitor getInstance();
}
