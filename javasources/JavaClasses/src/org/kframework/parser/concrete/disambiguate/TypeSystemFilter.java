package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


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
