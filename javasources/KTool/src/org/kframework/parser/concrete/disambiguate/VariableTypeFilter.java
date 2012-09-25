package org.kframework.parser.concrete.disambiguate;

import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.visitors.exceptions.VariableTypeClashException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class VariableTypeFilter extends BasicTransformer {

	private Map<String, String> variableTypes = null;

	public VariableTypeFilter(Map<String, String> types) {
		super("Variable type filter");
		this.variableTypes = types;
	}

	public ASTNode transform(Variable r) throws TransformerException {
		String correctSort = variableTypes.get(r.getName());
		if (correctSort == null)
			return r;
		if (DefinitionHelper.isSubsortedEq(r.getSort(), correctSort)) {
			Variable newV = new Variable(r);
			newV.setSort(correctSort);
			return newV;
		}
		String msg = "Variable " + r.getName() + " cannot have sort " + correctSort + " at this location.";
		KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation());
		throw new VariableTypeClashException(kex);
	}
}
