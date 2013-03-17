package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class RemoveBrackets extends CopyOnWriteTransformer {

	public RemoveBrackets() {
		super("Remove brackets");
	}

	@Override
	public ASTNode transform(Cast node) throws TransformerException {
		// System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
		if (node.isSyntactic())
			return node.getContent().accept(this);
		return super.transform(node);
	}

	@Override
	public ASTNode transform(Bracket node) throws TransformerException {
		// System.out.println("Remove: " + node.getFilename() + ":" + node.getLocation());
		return node.getContent().accept(this);
	}
}
