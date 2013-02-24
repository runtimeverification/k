package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class VariableReplaceTransformer extends BasicTransformer {

	private Map<Variable, Variable> generatedVariables;

	
	public VariableReplaceTransformer(String name) {
		super("Replace Variables");
		generatedVariables = new HashMap<Variable, Variable>();
	}

	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		Variable newVar = MetaK.getFreshVar(node.getSort());
		generatedVariables.put(newVar, node);
		return newVar;
	}
	
	public Map<Variable, Variable> getGeneratedVariables() {
		return generatedVariables;
	}
}
