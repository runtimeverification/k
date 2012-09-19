package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveAnonymousVariables extends CopyOnWriteTransformer {

	public ResolveAnonymousVariables() {
		super("Resolve anonymous variables");
	}
	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		if (MetaK.isAnonVar(node)) 
			return MetaK.getFreshVar(node.getSort());
		return node;
	}

}
