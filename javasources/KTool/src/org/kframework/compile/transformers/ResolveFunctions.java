package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
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
                node = addFunction(node);
			}
		}
        if (body instanceof KApp) {
            Term l = ((KApp)body).getLabel();
            if (l instanceof Constant) {
                String name = ((Constant) l).getValue();
                if (MetaK.isPredicateLabel(name)) {
                    node = addFunction(node);
                }
            }
        }
		return node;
	}

    private Rule addFunction(Rule node) {
        node = node.shallowCopy();
        node.setAttributes(node.getAttributes().shallowCopy());
        node.getAttributes().set("function", "");
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
