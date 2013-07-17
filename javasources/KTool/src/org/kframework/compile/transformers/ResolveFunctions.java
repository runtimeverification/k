package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Add the function attribute to rules which rewrite either a TermCons of
 * a production with a function or predicate attribute,
 * or a KApp of a KLabelConstant satisfying MetaK.isPredicateLabel.
 */
public class ResolveFunctions extends CopyOnWriteTransformer {

	public ResolveFunctions(Context context) {
		super("Resolve Functions", context);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		Term body = node.getBody();
		if (body instanceof Rewrite) {
			body = ((Rewrite) body).getLeft();
		}
		if (body instanceof TermCons) {
			Production prod = context.conses.get(((TermCons) body).getCons());
			if (prod.containsAttribute("function") || prod.containsAttribute("predicate")) {
				node = addFunction(node);
			}
		}
		if (body instanceof KApp) {
			Term l = ((KApp) body).getLabel();
			if (l instanceof KLabelConstant) {
				if (MetaK.isPredicateLabel(((KLabelConstant) l).getLabel())) {
					node = addFunction(node);
				}
			}
		}
		return node;
	}

	private Rule addFunction(Rule node) {
		node = node.shallowCopy();
		node.setAttributes(node.getAttributes().shallowCopy());
		node.putAttribute("function", "");
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

}
