package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;

public class TypeInferenceSupremumFilter extends BasicTransformer {

	public TypeInferenceSupremumFilter() {
		super("Type inference supremum");
		// TODO Auto-generated constructor stub
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {

		// choose the maximum from the list of ambiguities
		java.util.List<Term> terms = new ArrayList<Term>();
		for (Term trm1 : amb.getContents()) {
			boolean topSort = true;
			for (Term trm2 : amb.getContents()) {
				if (termsAlike(trm1, trm2))
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

	/**
	 * Returns true if the terms are of the same kind (Variable, TermCons...) If they are TermCons, then all the Items must be alike also.
	 * 
	 * @param trm1
	 *            First term to compare.
	 * @param trm2
	 *            Second term to compare.
	 * @return true or false weather they are alike.
	 */
	private static boolean termsAlike(Term trm1, Term trm2) {
		if (!trm1.getClass().equals(trm2.getClass()))
			return false;

		if (trm1 instanceof TermCons) {
			TermCons term1 = (TermCons) trm1;
			TermCons term2 = (TermCons) trm2;

			if (term1.getProduction().getItems().size() != term2.getProduction().getItems().size())
				return false;

			// check to see if every non terminal is subsorted-eq to the other term.
			// add 1 to left each time Sort1 < Sort2 and add 1 to right vice versa
			// if at least one of them is 0 at the end return true.
			int left = 0, right = 0;
			for (int i = 0; i < term1.getProduction().getItems().size(); i++) {
				ProductionItem itm1 = term1.getProduction().getItems().get(i);
				ProductionItem itm2 = term2.getProduction().getItems().get(i);

				if (itm1.getType() == ProductionType.TERMINAL && !itm1.equals(itm2))
					return false;
				else if (itm1.getType() == ProductionType.USERLIST) {
					if (itm2.getType() != ProductionType.USERLIST)
						return false;
					UserList ul1 = (UserList) itm1;
					UserList ul2 = (UserList) itm2;

					if (!ul1.getSeparator().equals(ul2.getSeparator()))
						return false;

					if (DefinitionHelper.isSubsorted(ul1.getSort(), ul2.getSort()))
						left++;
					else if (DefinitionHelper.isSubsorted(ul2.getSort(), ul1.getSort()))
						right++;
					else if (!ul1.getSort().equals(ul2.getSort()))
						return false;
				} else if (itm1.getType() == ProductionType.SORT) {
					if (itm2.getType() != ProductionType.SORT)
						return false;
					// only sort possible now.
					Sort srt1 = (Sort) itm1;
					Sort srt2 = (Sort) itm2;

					if (DefinitionHelper.isSubsorted(srt1.getName(), srt2.getName()))
						left++;
					else if (DefinitionHelper.isSubsorted(srt2.getName(), srt1.getName()))
						right++;
					else if (!srt1.equals(srt2))
						return false;
				}
			}
			if (right == 0 || left == 0)
				return true;
		}

		return true;
	}
}
