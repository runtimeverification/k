package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class PriorityFilter extends BasicTransformer {
	public PriorityFilter(Context context) {
		super("Priority filter", context);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (tc.getProduction() == null)
			System.err.println(this.getClass() + ":" + " cons not found." + tc.getCons());
		if (tc.getProduction().isListDecl()) {
			tc.getContents().set(0, (Term) tc.getContents().get(0).accept(new PriorityFilter2(tc, context)));
			tc.getContents().set(1, (Term) tc.getContents().get(1).accept(new PriorityFilter2(tc, context)));
		} else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
			for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
				if (tc.getProduction().getItems().get(i) instanceof Sort) {
					// look for the outermost element
					if ((i == 0 || i == tc.getProduction().getItems().size() - 1)
							&& (tc.getContents().get(j) instanceof TermCons || tc.getContents().get(j) instanceof Ambiguity)) {
						tc.getContents().set(j, (Term) tc.getContents().get(j).accept(new PriorityFilter2(tc, context)));
					}
					j++;
				}
			}
		}

		return super.transform(tc);
	}
}
