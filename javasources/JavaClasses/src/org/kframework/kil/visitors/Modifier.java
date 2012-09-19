package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;

public abstract class Modifier {
	public abstract ASTNode modify(ASTNode astNode);
}
