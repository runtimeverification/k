package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Variable;
import org.kframework.visitors.CopyOnWriteTransformer;

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
