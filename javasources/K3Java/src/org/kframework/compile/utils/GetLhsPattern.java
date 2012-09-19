package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
