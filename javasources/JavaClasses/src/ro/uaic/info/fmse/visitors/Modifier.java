package ro.uaic.info.fmse.visitors;

import ro.uaic.info.fmse.k.ASTNode;

public abstract class Modifier {
	public abstract ASTNode modify(ASTNode astNode);
}
