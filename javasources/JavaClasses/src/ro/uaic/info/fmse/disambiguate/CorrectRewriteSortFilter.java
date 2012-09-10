package ro.uaic.info.fmse.disambiguate;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class CorrectRewriteSortFilter extends BasicTransformer {

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
