package org.kframework.visitors;

import org.kframework.k.ASTNode;

public abstract class Modifier {
	public abstract ASTNode modify(ASTNode astNode);
}
