package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class PriorityFilter2 extends BasicHookWorker {

	private TermCons parent;

	public PriorityFilter2(TermCons parent, Context context) {
		super("Type system", context);
		this.parent = parent;
	}

	public PriorityFilter2(PriorityFilter2 pf, Context context) {
		super("Type system", context);
		this.parent = pf.parent;
	}

	public ASTNode transform(TermCons tc) throws TransformerException {
		String parentLabel = parent.getProduction().getKLabel();
		String localLabel = tc.getProduction().getKLabel();
		if (context.isPriorityWrong(parentLabel, localLabel)) {
			String msg = "Priority filter exception. Cannot use " + localLabel + " as a child of " + parentLabel;
			KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
			throw new PriorityException(kex);
		}

		return tc;
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		TransformerException exception = null;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = null;
			try {
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
		return node;
	}

	@Override
	public ASTNode transform(Term node) throws TransformerException {
		return node;
	}
}
