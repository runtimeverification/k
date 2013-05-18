package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.visitors.exceptions.VariableTypeClashException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.Map;

public class VariableTypeFilter extends BasicTransformer {

	private Map<String, String> variableTypes = null;

	public VariableTypeFilter(Map<String, String> types, DefinitionHelper definitionHelper) {
		super("Variable type filter", definitionHelper);
		this.variableTypes = types;
	}

	public ASTNode transform(Variable r) throws TransformerException {
		String correctSort = variableTypes.get(r.getName());
		if (correctSort == null)
			return r;
		if (definitionHelper.isSubsortedEq(r.getSort(), correctSort)) {
			Variable newV = new Variable(r);
			newV.setSort(correctSort);
			return newV;
		}
		String msg = "Variable " + r.getName() + " is contextually expected to have sort " + r.getSort() + " but it has been declared (or infered) of sort " + correctSort + ".";
		// String msg = "Variable " + r.getName() + " cannot have sort " + r.getSort() + " at this location. Expected sort " + correctSort + ".";
		KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation());
		throw new VariableTypeClashException(kex);
	}
}
