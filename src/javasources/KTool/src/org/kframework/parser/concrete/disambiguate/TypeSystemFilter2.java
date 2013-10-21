package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;

public class TypeSystemFilter2 extends BasicHookWorker {

	private String maxSort;

	public TypeSystemFilter2(String maxSort, org.kframework.kil.loader.Context context) {
		super("Type system", context);
		this.maxSort = maxSort;
	}

	public TypeSystemFilter2(TypeSystemFilter2 tsf, Context context) {
		super("Type system", context);
		this.maxSort = tsf.maxSort;
	}

	public ASTNode transform(Term trm) throws TransformerException {
		if (!trm.getSort().equals(KSorts.K) && !trm.getSort().equals(KSorts.KITEM)
                && !trm.getSort().equals(KSorts.KRESULT)) {
			if (!context.isSubsortedEq(maxSort, trm.getSort())) {
				KException kex = new KException(
                        ExceptionType.ERROR,
                        KExceptionGroup.CRITICAL,
                        "type error: unexpected term '" + trm + "' of sort '" + trm.getSort()
                                + "', expected sort '" + maxSort + "'.",
                        trm.getFilename(),
                        trm.getLocation());
				throw new TransformerException(kex);
			}
        }
		return trm;
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
	public ASTNode transform(Bracket node) throws TransformerException {
		node.setContent((Term) node.getContent().accept(this));
		return node;
	}

	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		Rewrite result = new Rewrite(node);
		result.replaceChildren(
				(Term) node.getLeft().accept(this),
				(Term) node.getRight().accept(this),
                context);
		return result;
	}
}
