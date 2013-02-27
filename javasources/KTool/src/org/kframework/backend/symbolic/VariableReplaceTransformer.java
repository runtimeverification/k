package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class VariableReplaceTransformer extends BasicTransformer {

	private Map<Variable, Variable> generatedVariables;
	private Set<String> vars;

	public VariableReplaceTransformer(String name) {
		super("Replace Variables");
		generatedVariables = new HashMap<Variable, Variable>();
		vars = new HashSet<String>();
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		Variable newVar = node;
		if (vars.contains(node.getName())) {
			newVar = MetaK.getFreshVar(node.getSort());
			generatedVariables.put(newVar, node);
		}

		vars.add(node.getName());
		return newVar;
	}

	public Map<Variable, Variable> getGeneratedVariables() {
		return generatedVariables;
	}
}
