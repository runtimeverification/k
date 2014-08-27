// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BinderSubstitutionTransformer;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.VariableCollector;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Visitor;

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
     * Field used for cashing the hash code
     */
    protected int hashCode = Utils.NO_HASHCODE;

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
     * applying a substitution in (in a binder sensitive way) .
     */
    public JavaSymbolicObject substituteWithBinders(
            Map<Variable, ? extends Term> substitution,
            TermContext context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        return (JavaSymbolicObject) accept(new BinderSubstitutionTransformer(substitution, context));
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * applying a substitution in (in a binder insensitive way) .
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
     * substituting variable (in a binder sensitive way) with term.
     */
    public JavaSymbolicObject substituteWithBinders(Variable variable, Term term, TermContext context) {
        return substituteWithBinders(Collections.singletonMap(variable, term), context);
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * substituting variable (in a binder insensitive way) with term.
     */
    public JavaSymbolicObject substitute(Variable variable, Term term, TermContext context) {
        return substitute(Collections.singletonMap(variable, term), context);
    }

    /**
     * Returns a {@code Set} view of the variables in this
     * {@code JavaSymbolicObject}.
     * <p>
     * When the set of variables has not been computed, this method will do the
     * computation instead of simply returning {@code null} as in
     * {@link JavaSymbolicObject#getVariableSet()}.
     */
    public Set<Variable> variableSet() {
        if (variableSet == null) {
            VariableCollector visitor = new VariableCollector();
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
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        throw new UnsupportedOperationException();
    }

    /**
     * Forces to recompute the cached set of variables in this
     * {@code JavaSymbolicObject}.
     */
    public void updateVariableSet() {
        variableSet = null;
        variableSet();
    }

    /**
     * Gets the cached set of variables in this {@code JavaSymbolicObject}.
     *
     * @return a set of variables in this {@code JavaSymbolicObject} if they
     *         have been computed; otherwise, {@code null}
     * @see JavaSymbolicObject#variableSet()
     */
    public Set<Variable> getVariableSet() {
        return variableSet;
    }

    public void setVariableSet(Set<Variable> variableSet) {
        this.variableSet = variableSet;
    }

    // TODO(YilongL): remove the comments below to enforce that every subclass
    // has implemented the following two methods properly
    //@Override
    //public abstract boolean equals(Object object);

    //@Override
    //public abstract int hashCode();

}
