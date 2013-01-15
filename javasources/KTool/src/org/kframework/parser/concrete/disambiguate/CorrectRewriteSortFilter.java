package org.kframework.parser.concrete.disambiguate;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class CorrectRewriteSortFilter extends BasicTransformer {

	public CorrectRewriteSortFilter() {
		super("Correct rewrite sort");
	}

	public ASTNode transform(Rewrite rw) throws TransformerException {

		if (rw.getSort().equals(MetaK.Constants.KList)) {
			String lsort = rw.getLeft().getSort();
			String rsort = rw.getRight().getSort();

			if (!lsort.equals(MetaK.Constants.KList) && !rsort.equals(MetaK.Constants.KList))
				rw.setSort("K");
		}

		return super.transform(rw);
	}
}
