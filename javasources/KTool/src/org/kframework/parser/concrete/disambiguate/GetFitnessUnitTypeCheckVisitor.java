package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;

/**
 * Check to see which branch of an ambiguity has less type errors
 * 
 * @author RaduFmse
 * 
 */
public class GetFitnessUnitTypeCheckVisitor extends GetFitnessUnitBasicVisitor {

	public GetFitnessUnitTypeCheckVisitor(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}

	@Override
	public void visit(TermCons tc) {

		// TODO: make this as a hard type checker where you throw exceptions every time you get a typing error
		super.visit(tc);

		if (tc.getProduction(definitionHelper).getItems().get(0).getType() == ProductionType.USERLIST) {
			UserList ulist = (UserList) tc.getProduction(definitionHelper).getItems().get(0);

			score += getFitnessUnit2(ulist.getSort(), tc.getContents().get(0));
			score += getFitnessUnit2(tc.getProduction(definitionHelper).getSort(), tc.getContents().get(1));
		} else {
			int j = 0;
			for (int i = 0; i < tc.getProduction(definitionHelper).getItems().size(); i++) {
				if (tc.getProduction(definitionHelper).getItems().get(i).getType() == ProductionType.SORT) {
					Sort sort = (Sort) tc.getProduction(definitionHelper).getItems().get(i);
					Term child = (Term) tc.getContents().get(j);
					score += getFitnessUnit2(sort.getName(), child);
					j++;
				}
			}
		}
	}

	@Override
	public void visit(Collection node) {
		super.visit(node);
		for (Term t : node.getContents()) {
			if (!definitionHelper.isSubsortedEq(node.getSort(definitionHelper), t.getSort(definitionHelper)))
				score += -1;
		}
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
	private int getFitnessUnit2(String declSort, Term childTerm) {
		if (childTerm instanceof Rewrite) {
			Rewrite rw = (Rewrite) childTerm;
			return getFitnessUnit2(declSort, rw.getLeft()) + getFitnessUnit2(declSort, rw.getRight());
		} else if (childTerm instanceof Ambiguity) {
			// if there is an ambiguity, choose only the subsorts (if that doesn't eliminate the node completely)
			return 0;
		} else if (childTerm instanceof Bracket) {
			Bracket br = (Bracket) childTerm;
			return getFitnessUnit2(declSort, br.getContent());
		}

		return getFitnessUnit3(declSort, childTerm.getSort(definitionHelper));
	}

	private int getFitnessUnit3(String declSort, String termSort) {
		int score;
		if (definitionHelper.isSubsortedEq(declSort, termSort))
			score = 0;
		// isSubsortEq(|"K", expect) ; (<?"K"> place <+ <?"K"> expect); !0
		else if (definitionHelper.isSubsortedEq("K", termSort) && (declSort.equals("K") || termSort.equals("K")))
			score = 0; // do nothing when you have a K
		else {
			score = -1;
		}
		// System.out.println("Score: (" + declSort + "," + termSort + "," + score + ")");
		return score;
	}

	@Override
	public GetFitnessUnitBasicVisitor getInstance() {
		return new GetFitnessUnitTypeCheckVisitor(definitionHelper);
	}
}
