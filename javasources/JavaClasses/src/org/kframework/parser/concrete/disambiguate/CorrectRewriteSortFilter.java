package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
