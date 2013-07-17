package org.kframework.kagreg;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class RenameVariablesTransformer extends CopyOnWriteTransformer {
	protected RenameStrategy renameStrategy;

	public RenameVariablesTransformer(RenameStrategy renameStrategy, Context context) {
		super("RenameVariablesTransformer", context);
		this.renameStrategy = renameStrategy;
		assert this.renameStrategy != null;
	}
	
	@Override
	public ASTNode transform(Variable variable) throws TransformerException {
		variable = (Variable)super.transform(variable);
		String oldName = variable.getName();
		if (oldName != null && oldName.startsWith("$")) {
			variable.setName(renameStrategy.getNewName(oldName));
		}
		return variable;
	}
}
