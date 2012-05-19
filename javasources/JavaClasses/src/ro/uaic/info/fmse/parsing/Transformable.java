package ro.uaic.info.fmse.parsing;

public interface Transformable {
	public ASTNode accept(Transformer visitor);
}
