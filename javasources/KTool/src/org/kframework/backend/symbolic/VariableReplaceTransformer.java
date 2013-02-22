package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class VariableReplaceTransformer extends BasicTransformer {

	private Map<Variable, Variable> generatedFor;

	
	public VariableReplaceTransformer(String name) {
		super("Replace Variables");
		generatedFor = new HashMap<Variable, Variable>();
	}

	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		Variable newVar = MetaK.getFreshVar(node.getSort());
		generatedFor.put(newVar, node);
		return newVar;
	}
	
	public Map<Variable, Variable> getGeneratedFor() {
		return generatedFor;
	}
}
