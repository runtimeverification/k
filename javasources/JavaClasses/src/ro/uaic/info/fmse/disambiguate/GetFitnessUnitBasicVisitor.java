package ro.uaic.info.fmse.disambiguate;

import ro.uaic.info.fmse.visitors.BasicVisitor;

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
