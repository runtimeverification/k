package ro.uaic.info.fmse.disambiguate;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class CorrectRewriteFilter extends BasicTransformer {

	public ASTNode transform(Ambiguity amb) {
		for (Term t : amb.getContents()) {
			if (t instanceof Rewrite) {
				return super.transform(t);
			}
		}

		return super.transform(amb);
	}
}
