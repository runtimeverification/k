package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;

public class CheckRewriteFilter extends BasicTransformer {
	public CheckRewriteFilter() {
		super("Priority filter");
	}

	TermCons parent = null;

	@Override
	public ASTNode transform(Rewrite rw) throws TransformerException {
		if (parent != null) {
			String msg = "Rewrite is not greedy. Use parentheses to set proper scope.";
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, rw.getFilename(), rw.getLocation());
			throw new PriorityException(kex);
		}

		parent = null;
		return super.transform(rw);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (tc.getProduction().isListDecl()) {
			Term t = tc.getContents().get(0);
			parent = t instanceof Rewrite || t instanceof Ambiguity ? tc : null;
			tc.getContents().set(0, (Term) t.accept(this));

			t = tc.getContents().get(1);
			parent = t instanceof Rewrite || t instanceof Ambiguity ? tc : null;
			tc.getContents().set(1, (Term) t.accept(this));
		} else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
			for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
				if (tc.getProduction().getItems().get(i).getType() == ProductionType.SORT) {
					// look for the outermost element
					if ((i == 0 || i == tc.getProduction().getItems().size() - 1) && (tc.getContents().get(j) instanceof Rewrite || tc.getContents().get(j) instanceof Ambiguity)) {
						parent = tc;
						tc.getContents().set(j, (Term) tc.getContents().get(j).accept(this));
					} else {
						parent = null;
						tc.getContents().set(j, (Term) tc.getContents().get(j).accept(this));
					}
					j++;
				}
			}
		}

		return transform((Term) tc);
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		TermCons lp = parent;
		TransformerException exception = null;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = null;
			try {
				if (t instanceof Rewrite || t instanceof Ambiguity)
					parent = lp;
				else
					parent = null;

				result = t.accept(this);
				terms.add((Term) result);
			} catch (TransformerException e) {
				exception = e;
			}
		}
		if (terms.isEmpty())
			throw exception;
		if (terms.size() == 1) {
			return terms.get(0);
		}
		node.setContents(terms);
		return transform((Term) node);
	}
}
