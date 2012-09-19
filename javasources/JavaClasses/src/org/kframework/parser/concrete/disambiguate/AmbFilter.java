package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class AmbFilter extends BasicTransformer {
	public AmbFilter() {
		super("Ambiguity filter");
	}

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
