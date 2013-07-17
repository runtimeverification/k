package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveAnonymousVariables extends CopyOnWriteTransformer {

	public ResolveAnonymousVariables(Context context) {
		super("Resolve anonymous variables", context);
	}
	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		if (MetaK.isAnonVar(node)) 
			return Variable.getFreshVar(node.getSort());
		return node;
	}

}
