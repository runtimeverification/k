package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KSequence;
import org.kframework.kil.MapItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CheckBinaryPrecedenceFilter extends BasicTransformer {
	public CheckBinaryPrecedenceFilter(Context context) {
		super("Check precedence for => and ~>", context);
	}

	TermCons parent = null;
	KSequence parentks = null;
	Term parentmi = null;

	@Override
	public ASTNode transform(Rewrite rw) throws TransformerException {
		if (parent != null || parentks != null || parentmi != null) {
			String msg = "Due to typing errors, rewrite is not greedy. Use parentheses to set proper scope.";
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, rw.getFilename(), rw.getLocation());
			throw new PriorityException(kex);
		}

		parent = null;
		parentks = null;
		parentmi = null;
		return transform((Term) rw);
	}

	@Override
	public ASTNode transform(MapItem mi) throws TransformerException {
		parent = null;
		parentks = null;

		Term t = mi.getKey();
		parentmi = t instanceof Rewrite || t instanceof Ambiguity ? mi : null;
		mi.setKey((Term) t.accept(this));

		t = mi.getValue();
		parentmi = t instanceof Rewrite || t instanceof Ambiguity ? mi : null;
		mi.setValue((Term) t.accept(this));

		parentks = null;
		parent = null;
		parentmi = null;
		return transform((Term) mi);
	}

	@Override
	public ASTNode transform(KSequence ks) throws TransformerException {
		if (parent != null || parentks != null) {
			String msg = "Due to typing errors, ~> is not greedy. Use parentheses to set proper scope.";
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getFilename(), ks.getLocation());
			throw new PriorityException(kex);
		}

		parent = null;
		parentmi = null;

		Term t = ks.getContents().get(0);
		parentks = t instanceof Rewrite || t instanceof Ambiguity ? ks : null;
		ks.getContents().set(0, (Term) t.accept(this));

		t = ks.getContents().get(1);
		parentks = t instanceof Rewrite || t instanceof Ambiguity || t instanceof KSequence ? ks : null;
		ks.getContents().set(1, (Term) t.accept(this));

		parentks = null;
		parent = null;
		parentmi = null;
		return transform((Term) ks);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (tc.getProduction().isListDecl()) {
			Term t = tc.getContents().get(0);
			parent = t instanceof Rewrite || t instanceof Ambiguity || t instanceof KSequence ? tc : null;
			parentks = null;
			parentmi = null;
			tc.getContents().set(0, (Term) t.accept(this));

			t = tc.getContents().get(1);
			parent = t instanceof Rewrite || t instanceof Ambiguity || t instanceof KSequence ? tc : null;
			parentks = null;
			tc.getContents().set(1, (Term) t.accept(this));
		} else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
			for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
				if (tc.getProduction().getItems().get(i) instanceof Sort) {
					// look for the outermost element
					Term t = tc.getContents().get(j);
					if ((i == 0 || i == tc.getProduction().getItems().size() - 1) && (t instanceof Rewrite || t instanceof Ambiguity || t instanceof KSequence)) {
						parent = tc;
						parentks = null;
						tc.getContents().set(j, (Term) t.accept(this));
					} else {
						parent = null;
						parentks = null;
						tc.getContents().set(j, (Term) t.accept(this));
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
		KSequence ks = parentks;
		Term mi = parentmi;
		TransformerException exception = null;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = null;
			try {
				if (t instanceof Rewrite || t instanceof Ambiguity || t instanceof KSequence) {
					parent = lp;
					parentks = ks;
					parentmi = mi;
				}

				result = t.accept(this);
				terms.add((Term) result);
			} catch (TransformerException e) {
				exception = e;
			}
			parent = null;
			parentks = null;
			parentmi = null;
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
