package ro.uaic.info.fmse.visitors;

import ro.uaic.info.fmse.k.ASTNode;

public interface Transformable {
	public ASTNode accept(Transformer visitor);
}
