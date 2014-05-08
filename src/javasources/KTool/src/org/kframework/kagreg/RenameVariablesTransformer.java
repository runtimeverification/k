// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kagreg;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class RenameVariablesTransformer extends CopyOnWriteTransformer {
    protected RenameStrategy renameStrategy;

    public RenameVariablesTransformer(RenameStrategy renameStrategy, Context context) {
        super("RenameVariablesTransformer", context);
        this.renameStrategy = renameStrategy;
        assert this.renameStrategy != null;
    }
    
    @Override
    public ASTNode visit(Variable variable, Void _)  {
        variable = (Variable)super.visit(variable, _);
        String oldName = variable.getName();
        if (oldName != null && oldName.startsWith("$")) {
            variable.setName(renameStrategy.getNewName(oldName));
        }
        return variable;
    }
}
