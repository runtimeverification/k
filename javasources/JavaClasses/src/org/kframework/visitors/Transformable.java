package org.kframework.visitors;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;

public interface Transformable {
	public ASTNode accept(Transformer visitor) throws TransformerException;
}
