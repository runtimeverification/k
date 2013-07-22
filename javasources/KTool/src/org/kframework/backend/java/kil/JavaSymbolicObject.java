package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.kil.ASTNode;

import java.util.Set;


/**
 * Root of the Java Rewrite Engine internal representation class hierarchy.
 *
 * @author: AndreiS
 */
public abstract class JavaSymbolicObject extends ASTNode implements Visitable {

    /**
     * Returns a {@code Set} view of the variables in this java symbolic object.
     */
    public Set<Variable> variableSet() {
        VariableVisitor visitor = new VariableVisitor();
        accept(visitor);
        return visitor.getVariableSet();
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(org.kframework.kil.visitors.Transformer transformer)
            throws org.kframework.kil.visitors.exceptions.TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(org.kframework.kil.visitors.Visitor visitor) {
        throw new UnsupportedOperationException();
    }
}
