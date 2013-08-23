package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.visitors.exceptions.VariableTypeClashException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.Map;

public class VariableTypeFilter extends BasicTransformer {

	private Map<String, Variable> variableTypes = null;

	public VariableTypeFilter(Map<String, Variable> types, Context context) {
		super("Variable type filter", context);
		this.variableTypes = types;
	}

	public ASTNode transform(Variable r) throws TransformerException {
		Variable correctVar = variableTypes.get(r.getName());
		if (correctVar == null)
			return r;
		if (context.isSubsortedEq(r.getExpectedSort(), correctVar.getExpectedSort())) {
			Variable newV = new Variable(r);
			newV.setSort(correctVar.getSort());
			newV.setExpectedSort(correctVar.getExpectedSort());
			newV.setSyntactic(correctVar.isSyntactic());
			return newV;
		}
		String msg = "Variable " + r.getName() + " is contextually expected to have sort " + r.getExpectedSort();
		msg += " but it has been declared (or infered) of sort " + correctVar.getExpectedSort() + ".";
		KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation());
		throw new VariableTypeClashException(kex);
	}
}
