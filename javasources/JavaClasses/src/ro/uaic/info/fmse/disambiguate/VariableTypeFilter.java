package ro.uaic.info.fmse.disambiguate;

import java.util.Map;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.exceptions.VariableTypeClashException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

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
