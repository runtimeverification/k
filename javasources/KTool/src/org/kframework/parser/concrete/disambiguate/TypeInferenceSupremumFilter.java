package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class TypeInferenceSupremumFilter extends BasicTransformer {

	public TypeInferenceSupremumFilter(DefinitionHelper definitionHelper) {
		super("Type inference supremum", definitionHelper);
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {
		// find the groups of terms alike

		Set<Term> processed = new HashSet<Term>();
		Set<Term> maxterms = new HashSet<Term>();
		for (Term t : amb.getContents()) {
			if (!processed.contains(t)) {
				processed.add(t);
				Set<Term> group = new HashSet<Term>();
				group.add(t);
				for (Term t2 : amb.getContents()) {
					if (!processed.contains(t2) && termsAlike_simple(t, t2)) {
						processed.add(t2);
						group.add(t2);
					}
				}

				// found a group of terms that are alike
				// alike means they have the same arity, same position for terminals and non terminals
				if (t instanceof TermCons) {
					// finally, try to find the minimums
					for (Term tm2 : group) {
						boolean min = true;
						Production tcBig = ((TermCons) tm2).getProduction(definitionHelper);
						for (Term tm22 : group) {
							Production tcSmall = ((TermCons) tm22).getProduction(definitionHelper);
							if (tm2 != tm22 && isSubsorted(tcBig, tcSmall)) {
								min = false;
								break;
							}
						}
						if (min)
							maxterms.add(tm2);
					}
				} else if (t instanceof Variable) {
					// for variables only, find maximum
					for (Term t1 : group) {
						boolean max = true;
						for (Term t2 : group)
							if (t1 != t2 && definitionHelper.isSubsorted(t2.getSort(definitionHelper), t1.getSort(definitionHelper)))
								max = false;
						if (max)
							maxterms.add(t1);
					}
				} else
					maxterms.addAll(group);
			}
		}

		if (maxterms.size() == 1) {
			return maxterms.iterator().next().accept(this);
		} else if (maxterms.size() > 1)
			amb.setContents(new ArrayList<Term>(maxterms));

		return super.transform(amb);
	}

	private boolean isSubsorted(Production big, Production small) {
		if (big == small)
			return false;
		if (big.getItems().size() != small.getItems().size())
			return false;
		if (!definitionHelper.isSubsortedEq(big.getSort(), small.getSort()))
			return false;
		for (int i = 0; i < big.getItems().size(); i++) {
			if (big.getItems().get(i).getType() != small.getItems().get(i).getType()) {
				return false;
			} else if (big.getItems().get(i).getType() == ProductionType.SORT) {
				String bigSort = ((Sort) big.getItems().get(i)).getName();
				String smallSort = ((Sort) small.getItems().get(i)).getName();
				if (!definitionHelper.isSubsortedEq(bigSort, smallSort))
					return false;
			} else if (big.getItems().get(i).getType() == ProductionType.USERLIST) {
				String bigSort = ((UserList) big.getItems().get(i)).getSort();
				String smallSort = ((UserList) small.getItems().get(i)).getSort();
				if (!definitionHelper.isSubsortedEq(bigSort, smallSort))
					return false;
			} else
				continue;
		}
		return true;
	}

	private boolean termsAlike_simple(Term trm1, Term trm2) {
		if (!trm1.getClass().equals(trm2.getClass()))
			return false;

		if (trm1 instanceof TermCons) {
			TermCons term1 = (TermCons) trm1;
			TermCons term2 = (TermCons) trm2;

			// check to see if the two terms have the same arity
			if (term1.getProduction(definitionHelper).getItems().size() != term2.getProduction(definitionHelper).getItems().size())
				return false;

			if (!term1.getProduction(definitionHelper).getKLabel().equals(term2.getProduction(definitionHelper).getKLabel()))
				return false;

			for (int i = 0; i < term1.getProduction(definitionHelper).getItems().size(); i++) {
				ProductionItem itm1 = term1.getProduction(definitionHelper).getItems().get(i);
				ProductionItem itm2 = term2.getProduction(definitionHelper).getItems().get(i);

				if (itm1.getType() == ProductionType.TERMINAL && !itm1.equals(itm2))
					return false;
				else if (itm1.getType() == ProductionType.USERLIST) {
					if (itm2.getType() != ProductionType.USERLIST)
						return false;
					UserList ul1 = (UserList) itm1;
					UserList ul2 = (UserList) itm2;

					if (!ul1.getSeparator().equals(ul2.getSeparator()))
						return false;
				} else if (itm1.getType() == ProductionType.SORT) {
					if (itm2.getType() != ProductionType.SORT)
						return false;
				}
			}
		}

		return true;
	}
}
