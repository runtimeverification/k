package org.kframework.disambiguate;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Rewrite;
import org.kframework.visitors.BasicTransformer;

public class CorrectRewriteSortFilter extends BasicTransformer {

	public CorrectRewriteSortFilter() {
		super("Correct rewrite sort");
	}

	public ASTNode transform(Rewrite rw) throws TransformerException {

		if (rw.getSort().equals("List{K}")) {
			String lsort = rw.getLeft().getSort();
			String rsort = rw.getRight().getSort();

			if (!lsort.equals("List{K}") && !rsort.equals("List{K}"))
				rw.setSort("K");
		}

		return super.transform(rw);
	}
}
