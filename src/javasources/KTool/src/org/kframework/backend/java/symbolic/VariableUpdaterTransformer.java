package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.kil.ASTNode;

/**
 * Recomputes the set of variables contained in each node of the AST.
 * 
 * @author Traian
 */
public class VariableUpdaterTransformer extends LocalTransformer {

    @Override
    protected ASTNode transform(JavaSymbolicObject object) {
        object.updateVariableSet();
        return object;
    }

}
