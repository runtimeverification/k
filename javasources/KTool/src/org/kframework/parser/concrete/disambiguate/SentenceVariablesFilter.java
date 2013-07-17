package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.visitors.exceptions.VariableTypeClashException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * Remove meta-variables from the configuration.
 * 
 * @author radu
 * 
 */
public class SentenceVariablesFilter extends BasicTransformer {
	private boolean config = false;

	public SentenceVariablesFilter(org.kframework.kil.loader.Context context) {
		super("Sentence Variable Filter", context);
	}

	public ASTNode transform(Configuration cfg) throws TransformerException {
		config = true;
		return super.transform(cfg);
	}

	public ASTNode transform(org.kframework.kil.Context cfg) throws TransformerException {
		config = false;
		return super.transform(cfg);
	}

	public ASTNode transform(Rule cfg) throws TransformerException {
		config = false;
		return super.transform(cfg);
	}

	public ASTNode transform(Syntax cfg) throws TransformerException {
		config = false;
		return cfg;
	}

	public ASTNode transform(Variable var) throws TransformerException {
		if (config) {
			if (!var.getName().startsWith("$")) {
				String msg = "In the configuration you can only have external variables, not: '" + var.getName() + "' (starts with '$').";
				KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getFilename(), var.getLocation());
				throw new VariableTypeClashException(kex);
			}
		} else {
			if (var.getName().startsWith("$")) {
				String msg = "You can have external variables only in the configuration: '" + var.getName() + "' (starts with '$').";
				KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getFilename(), var.getLocation());
				throw new VariableTypeClashException(kex);
			}
		}
		return var;
	}
}
