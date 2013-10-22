package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class RemoveSyntacticCasts extends CopyOnWriteTransformer {

	public RemoveSyntacticCasts(Context context) {
		super("Remove syntactic casts", context);
	}

	@Override
	public ASTNode transform(Cast node) throws TransformerException {
		// System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
		if (node.isSyntactic())
			return node.getContent().accept(this);
		return super.transform(node);
	}
}
