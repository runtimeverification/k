package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class GetLhsPattern extends CopyOnWriteTransformer {
	public GetLhsPattern(Context context) {
		super("Get Left-hand-side pattern", context);
	}
	
	public GetLhsPattern(String s, Context context) {
		super(s, context);
	}
	
	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return node.getLeft();
	}

}
