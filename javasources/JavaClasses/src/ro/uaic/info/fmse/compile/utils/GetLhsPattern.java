package ro.uaic.info.fmse.compile.utils;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

public class GetLhsPattern extends CopyOnWriteTransformer {
	public GetLhsPattern() {
		super("Get Left-hand-side pattern");
	}
	
	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return node.getLeft();
	}

}
