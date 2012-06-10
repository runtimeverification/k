package ro.uaic.info.fmse.disambiguate;

import java.util.Map.Entry;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class VariableTypeInferenceFilter extends BasicTransformer {

	public ASTNode transform(Rule r) {

		CollectVariablesVisitor vars = new CollectVariablesVisitor();
		r.accept(vars);

		// choose the minimum from the list for each variable name
		for (Entry<String, java.util.List<Variable>> varEntry : vars.getVars().entrySet()) {
			java.util.List<Variable> varList = varEntry.getValue();

			Variable minimum = varList.get(0);
			for (Variable v : varList)
				if (DefinitionHelper.isSubsorted(minimum.getSort(), v.getSort()))
					minimum = v;

			for (Variable v : varList)
				v.setSort(minimum.getSort());
		}

		return r;
	}
}
