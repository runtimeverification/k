package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ConstantsReplaceTransformer extends BasicTransformer {
	private Map<Variable, Constant> generatedSV;

	
	public  ConstantsReplaceTransformer(String name) {
		super("Replace Constants");
		generatedSV = new HashMap<Variable, Constant>();
	}

	
	@Override
	public ASTNode transform(Constant node) throws TransformerException {
		Variable newVar = MetaK.getFreshVar(node.getSort());
		generatedSV.put(newVar, node);
		return newVar;
	}
	
	public Map<Variable, Constant> getGeneratedSV() {
		return generatedSV;
	}
}
