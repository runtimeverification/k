package ro.uaic.info.fmse.disambiguate;

import java.util.ArrayList;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class BestFitFilter extends BasicTransformer {

	public ASTNode transform(Ambiguity amb) {

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
			return terms.get(0).accept(this);
		else
			amb.setContents(terms);

		return super.transform(amb);
	}

	/**
	 * Get the score for one term found under the ambiguity.
	 * 
	 * @param t
	 *            the term found under the ambiguity.
	 * @return an integer representing the score.
	 */
	private int getFitnessUnit(Term t) {
		if (t instanceof TermCons) {
			int score = 0;
			TermCons tc = (TermCons) t;

			if (tc.getProduction().getItems().get(0).getType() == ProductionType.USERLIST) {
				UserList ulist = (UserList) tc.getProduction().getItems().get(0);

				score += getFitnessUnit2(ulist.getSort(), tc.getContents().get(0).getSort());
				score += getFitnessUnit2(tc.getProduction().getSort(), tc.getContents().get(1).getSort());
			} else {
				int j = 0;
				for (int i = 0; i < tc.getProduction().getItems().size(); i++) {
					if (tc.getProduction().getItems().get(i).getType() == ProductionType.SORT) {
						Sort sort = (Sort) tc.getProduction().getItems().get(i);
						Term child = (Term) tc.getContents().get(j);
						score += getFitnessUnit2(sort.getSort(), child.getSort());
						j++;
					}
				}
			}
			return score;
		}
		return 0;
	}

	/**
	 * Get the score for two sorts
	 * 
	 * @param declSort
	 *            - the sort declared in the production.
	 * @param termSort
	 *            - the sort found in the term.
	 * @return
	 */
	// private int getFitnessUnit2(String declSort, String termSort) {
	// if (declSort.equals("K") || declSort.equals("List{K}") || termSort.equals("K") || termSort.equals("List{K}"))
	// return 0; // do nothing when you have a K
	// else if (declSort.equals(termSort))
	// return 2;
	// else if (DefinitionHelper.isSubsorted(declSort, termSort)) {
	// return 1;
	// } else
	// return -1;
	// }
	// TODO: this is so wrong, but it works :-??
	private int getFitnessUnit2(String declSort, String termSort) {
		if (declSort.equals(termSort) || DefinitionHelper.isSubsorted(declSort, termSort))
			return 1;
		else if ((DefinitionHelper.isSubsorted("K", termSort) || termSort.equals("K")) && (DefinitionHelper.isSubsorted("K", declSort) || declSort.equals("K")))
			return 0; // do nothing when you have a K
		else
			return -1;
	}
}
