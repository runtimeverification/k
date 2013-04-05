package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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

	public TypeInferenceSupremumFilter() {
		super("Type inference supremum");
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
				if (t instanceof TermCons) {
					// find the LUB for every position
					TermCons tc = (TermCons) t;
					List<String> lub = new ArrayList<String>(tc.getProduction().getItems().size());

					for (int i = 0; i < tc.getProduction().getItems().size(); i++) {
						lub.add("");
						Set<String> collect = new HashSet<String>();
						if (tc.getProduction().getItems().get(i).getType() == ProductionType.SORT) {
							for (Term tt : group) {
								TermCons ttc = (TermCons) tt;
								Production p = ttc.getProduction();
								collect.add(((Sort) p.getItems().get(i)).getName());
							}
						} else if (tc.getProduction().getItems().get(i).getType() == ProductionType.USERLIST) {
							for (Term tt : group) {
								TermCons ttc = (TermCons) tt;
								collect.add(ttc.getProduction().getSort());
							}
						}
						String lubSort = DefinitionHelper.getLUBSort(collect);
						if (lubSort == null) {
							// couldn't find a LUB sort, leave it ambiguous
							maxterms.addAll(group);
							group.clear();
							break;
						}
						lub.set(i, lubSort);
					}

					// add only the term that has all the sorts as LUB
					Set<Term> maxterms2 = new HashSet<Term>();
					for (Term tt : group) {
						TermCons ttc = (TermCons) tt;
						boolean allLub = true;
						for (int i = 0; i < ttc.getProduction().getItems().size(); i++) {
							if (ttc.getProduction().getItems().get(i).getType() == ProductionType.SORT) {
								if (!((Sort) ttc.getProduction().getItems().get(i)).getName().equals(lub.get(i))) {
									allLub = false;
									break;
								}
							} else if (ttc.getProduction().getItems().get(i).getType() == ProductionType.USERLIST) {
								if (!ttc.getProduction().getSort().equals(lub.get(i))) {
									allLub = false;
									break;
								}
							}
						}
						if (allLub) {
							maxterms2.add(tt);
						}
					}
					if (maxterms2.isEmpty()) {
						// this means that I couldn't find a term that contains all the LUB sorts
						// leave it ambiguous
						maxterms.addAll(group);
					} else {
						maxterms.addAll(maxterms2);
					}
				} else if (t instanceof Variable) {
					// find maximum for variables only
					for (Term t1 : group) {
						boolean max = true;
						for (Term t2 : group) {
							if (t1 != t2 && DefinitionHelper.isSubsorted(t2.getSort(), t1.getSort())) {
								max = false;
							}
						}
						if (max) {
							maxterms.add(t1);
						}
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

	private static boolean termsAlike_simple(Term trm1, Term trm2) {
		if (!trm1.getClass().equals(trm2.getClass()))
			return false;

		if (trm1 instanceof TermCons) {
			TermCons term1 = (TermCons) trm1;
			TermCons term2 = (TermCons) trm2;

			// check to see if the two terms have the same arity
			if (term1.getProduction().getItems().size() != term2.getProduction().getItems().size())
				return false;

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
				} else if (itm1.getType() == ProductionType.SORT) {
					if (itm2.getType() != ProductionType.SORT)
						return false;
				}
			}
		}

		return true;
	}
}
