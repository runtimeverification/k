package ro.uaic.info.fmse.disambiguate;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class AmbFilter extends BasicTransformer {
	public ASTNode transform(Ambiguity amb) throws TransformerException {
		String msg = "";

		for (ASTNode variant : amb.getContents()) {
			if (variant instanceof TermCons) {
				TermCons tc = (TermCons) variant;
				Production prod = DefinitionHelper.conses.get(tc.getCons());
				for (ProductionItem i : prod.getItems())
					msg += i + " ";
				msg += "(" + tc.getCons() + "), ";
			} else {
				msg += variant.toString() + ", ";
			}
		}
		msg = msg.substring(0, msg.length() - 2);
		msg += "    Arbitrarily choosing the first.";
		GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.PARSER, "Parsing ambiguity between: " + msg, amb.getFilename(), amb.getLocation(), 0));

		ASTNode astNode = amb.getContents().get(0);

		return astNode.accept(this);
	}
}
