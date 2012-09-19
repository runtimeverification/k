package org.kframework.disambiguate;

import java.util.ArrayList;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Production;
import org.kframework.k.Rewrite;
import org.kframework.k.Sort;
import org.kframework.k.Term;
import org.kframework.k.TermCons;
import org.kframework.k.UserList;
import org.kframework.k.ProductionItem.ProductionType;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.BasicTransformer;


public class TypeSystemFilter extends BasicTransformer {

	public TypeSystemFilter() {
		super("Type system");
		// TODO Auto-generated constructor stub
	}

	public ASTNode transform(TermCons tc) throws TransformerException {

		// choose only the allowed subsorts for a TermCons
		if (tc.getProduction().getItems().get(0).getType() == ProductionType.USERLIST) {
			UserList ulist = (UserList) tc.getProduction().getItems().get(0);
			tc.getContents().set(0, applyTypeFilter(tc.getContents().get(0), ulist.getSort()));
			tc.getContents().set(1, applyTypeFilter(tc.getContents().get(1), tc.getProduction().getSort()));

		} else {
			int j = 0;
			Production prd = tc.getProduction();
			for (int i = 0; i < prd.getItems().size(); i++) {
				if (prd.getItems().get(i).getType() == ProductionType.SORT) {
					Sort sort = (Sort) prd.getItems().get(i);
					Term child = (Term) tc.getContents().get(j);
					tc.getContents().set(j, applyTypeFilter(child, sort.getName()));
					j++;
				}
			}
		}

		return super.transform(tc);
	}

	private Term applyTypeFilter(Term t, String maxSort) {
		// apply under rewrites
		if (t instanceof Rewrite) {
			Rewrite rw = (Rewrite) t;
			rw.setLeft(applyTypeFilter(rw.getLeft(), maxSort));
			rw.setRight(applyTypeFilter(rw.getRight(), maxSort));
		} else if (t instanceof Ambiguity) {
			// if there is an ambiguity, choose only the subsorts (if that doesn't eliminate the node completely)
			Ambiguity amb = (Ambiguity) t;
			java.util.List<Term> terms = new ArrayList<Term>();
			for (Term trm : amb.getContents()) {
				if (maxSort.equals(trm.getSort()) || DefinitionHelper.isSubsorted(maxSort, trm.getSort())) {
					terms.add(trm);
				}
			}

			if (terms.size() == 1)
				t = terms.get(0);
			else if (terms.size() > 1)
				amb.setContents(terms);
		}
		return t;
	}
}
