package org.kframework.parser.concrete.disambiguate;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

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
		UnparserFilter unparserFilter = new UnparserFilter();
		unparserFilter.visit(amb);
		GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.PARSER, "Parsing ambiguity between: " + msg + " in the following AST: \n" + unparserFilter.getResult(), getName(), amb.getFilename(), amb.getLocation()));

		ASTNode astNode = amb.getContents().get(0);

		return astNode.accept(this);
	}
}
