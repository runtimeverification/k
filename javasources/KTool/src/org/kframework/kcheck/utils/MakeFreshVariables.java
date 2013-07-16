package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class MakeFreshVariables extends CopyOnWriteTransformer {

	private List<Variable> variables;

	public MakeFreshVariables(Context context, List<Variable> vars) {
		super("Replace a list of variables with symbolic values", context);
		this.variables = vars;
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		if (AddCircularityRules.varInList(node, variables)) {
			return new AddSymbolicK(context).freshSymSortId(node.getSort(), node.getName());
		}
		return super.transform(node);
	}
}
