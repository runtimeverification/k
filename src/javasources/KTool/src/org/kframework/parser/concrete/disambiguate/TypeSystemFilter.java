package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class TypeSystemFilter extends BasicTransformer {

	public TypeSystemFilter(Context context) {
		super("Type system", context);
	}

	public ASTNode transform(TermCons tc) throws TransformerException {
		// choose only the allowed subsorts for a TermCons
		if (tc.getProduction().getItems().get(0) instanceof UserList) {
			UserList ulist = (UserList) tc.getProduction().getItems().get(0);
			tc.getContents().set(0, (Term) tc.getContents().get(0).accept(new TypeSystemFilter2(ulist.getSort(), context)));
			tc.getContents().set(1, (Term) tc.getContents().get(1).accept(new TypeSystemFilter2(tc.getProduction().getSort(), context)));
		} else {
			int j = 0;
			Production prd = tc.getProduction();
			for (int i = 0; i < prd.getItems().size(); i++) {
				if (prd.getItems().get(i) instanceof Sort) {
					Sort sort = (Sort) prd.getItems().get(i);
					Term child = (Term) tc.getContents().get(j);
					tc.getContents().set(j, (Term) child.accept(new TypeSystemFilter2(sort.getName(), context)));
					j++;
				}
			}
		}

		return super.transform(tc);
	}

	public ASTNode transform(Cast cast) throws TransformerException {
		cast.setContent((Term) cast.getContent().accept(new TypeSystemFilter2(cast.getSort(), context)));
		return super.transform(cast);
	}
}
