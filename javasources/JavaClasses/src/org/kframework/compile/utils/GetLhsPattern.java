package org.kframework.compile.utils;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Rewrite;
import org.kframework.visitors.CopyOnWriteTransformer;

public class GetLhsPattern extends CopyOnWriteTransformer {
	public GetLhsPattern() {
		super("Get Left-hand-side pattern");
	}
	
	public GetLhsPattern(String s) {
		super(s);
	}
	
	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return node.getLeft();
	}

}
