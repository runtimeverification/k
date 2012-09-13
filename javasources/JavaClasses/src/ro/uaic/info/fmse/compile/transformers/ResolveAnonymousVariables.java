package ro.uaic.info.fmse.compile.transformers;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

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
