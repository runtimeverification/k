package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.kil.ASTNode;

import java.io.Serializable;
import java.util.Collections;
import java.util.Map;
import java.util.Set;


/**
 * Root of the Java Rewrite Engine internal representation class hierarchy.
 *
 * @author AndreiS
 */
public abstract class JavaSymbolicObject extends ASTNode
        implements Transformable, Visitable, Serializable {

    /**
     * AndreiS: serializing this field causes a NullPointerException when hashing a de-serialized
     * Variable (the variable has all fields set to null at the moment of hashing).
     */
    transient Set<Variable> variableSet = null;

    /**
     * Returns {@code true} if this JavaSymbolicObject does not contain any variables.
     */
    public boolean isGround() {
        return variableSet().isEmpty();
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * applying substitution.
     */
    public JavaSymbolicObject substitute(
            Map<Variable, ? extends Term> substitution,
            TermContext context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        return (JavaSymbolicObject) accept(new SubstitutionTransformer(substitution, context));
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * substituting variable with term.
     */
    public JavaSymbolicObject substitute(Variable variable, Term term, TermContext context) {
        return substitute(Collections.singletonMap(variable, term), context);
    }

    /**
     * Returns a {@code Set} view of the variables in this java symbolic object.
     */
    public Set<Variable> variableSet() {
        if (variableSet == null) {
            VariableVisitor visitor = new VariableVisitor();
            accept(visitor);
            variableSet = visitor.getVariableSet();
        }
        return variableSet;
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

    public void updateVariableSet() {
        variableSet = null;
        variableSet();
    }

    public Set<Variable> getVariableSet() {
        return variableSet;
    }

    public void setVariableSet(Set<Variable> variableSet) {
        this.variableSet = variableSet;
    }

    //@Override
    //public abstract boolean equals(Object object);

    //@Override
    //public abstract int hashCode();

}
