package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveFunctions extends CopyOnWriteTransformer {

	public ResolveFunctions() {
		super("Resolve Functions");
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		Term body = node.getBody();
		if (body instanceof Rewrite) {
			body = ((Rewrite) body).getLeft();
		}
		if (body instanceof TermCons) {
			Production prod = DefinitionHelper.conses.get(((TermCons)body).getCons());
			if (prod.getAttributes().containsKey("function")) {
				node = node.shallowCopy();
				node.setAttributes(node.getAttributes().shallowCopy());
				node.getAttributes().set("function", "");
			}
		}
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}
	
}
