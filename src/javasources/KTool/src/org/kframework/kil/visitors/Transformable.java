package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.exceptions.TransformerException;

public interface Transformable {
	public ASTNode accept(Transformer transformer) throws TransformerException;
}
