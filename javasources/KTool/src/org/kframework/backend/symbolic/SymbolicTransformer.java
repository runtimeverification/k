package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * This transformer applies some mechanical steps to the semantics 
 * of a programming language in order to transform it into a 
 * symbolic semantics.r
 */
public class SymbolicTransformer extends BasicTransformer {

	public SymbolicTransformer(String name) {
		super("Symbolic Transformer");
	}

	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		// TODO Auto-generated method stub
		
		LineariseTransformer lt = new LineariseTransformer("Linearise Transformer");
		Rule newRule = (Rule) lt.transform(node);
		
		return newRule;
	}
}
