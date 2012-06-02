package ro.uaic.info.fmse.loader;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class AmbFilter extends BasicTransformer {
	public ASTNode transform(Ambiguity amb) {
		String msg = "Warning! Parsing ambiguity at: " + amb.getLocation() + " in file: " + amb.getFilename() + "\n";
		msg += "    Ambiguity between: ";

		for (ASTNode variant : amb.getContents()) {
			if (variant instanceof TermCons) {
				TermCons tc = (TermCons) variant;
				Production prod = DefinitionHelper.conses.get("\"" + tc.getCons() + "\"");
				for (ProductionItem i : prod.getItems())
					msg += i + " ";
				msg += "(" + tc.getCons() + "), ";
			} else {
				msg += variant.getClass().toString() + ", ";
			}
		}
		msg = msg.substring(0, msg.length() - 2);
		msg += "    Arbitrarily choosing the first.";
		ro.uaic.info.fmse.utils.errors.Error.silentReport(msg);

		ASTNode astNode = amb.getContents().get(0);

		return astNode.accept(this);
	}
}
