package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rewrite;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class GetLhsPattern extends CopyOnWriteTransformer {
	public GetLhsPattern(DefinitionHelper definitionHelper) {
		super("Get Left-hand-side pattern", definitionHelper);
	}
	
	public GetLhsPattern(String s, DefinitionHelper definitionHelper) {
		super(s, definitionHelper);
	}
	
	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return node.getLeft();
	}

}
