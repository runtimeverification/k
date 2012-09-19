package org.kframework.disambiguate;

import java.util.Map;

import org.kframework.exceptions.TransformerException;
import org.kframework.exceptions.VariableTypeClashException;
import org.kframework.k.ASTNode;
import org.kframework.k.Variable;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.BasicTransformer;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;

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
		KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation(), 0);
		throw new VariableTypeClashException(kex);
	}
}
