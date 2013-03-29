package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveSymbolicInputStream extends CopyOnWriteTransformer {

	public ResolveSymbolicInputStream() {
		super("Resolve input stream for symbolic execution");
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		
		ResolveInputStreamCell risc = new ResolveInputStreamCell();
		Term content = (Term) node.getBody().accept(risc);
		
		node.shallowCopy();
		node.setBody(content);
		return node;
	}
}
