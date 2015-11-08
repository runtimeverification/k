// Copyright (c) 2013-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BinderSubstitutionTransformer;
import org.kframework.backend.java.symbolic.IncrementalCollector;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.visitors.Visitor;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import org.pcollections.HashTreePSet;
import org.pcollections.PSet;


/**
 * Root of the Java Rewrite Engine internal representation class hierarchy.
 *
 * @author AndreiS
 */
public abstract class JavaSymbolicObject<T extends JavaSymbolicObject<T>> extends ASTNode
        implements Transformable, Visitable {

    /**
     * Field used for caching the hash code
     */
    protected transient int hashCode = Constants.NO_HASHCODE;

    /**
     * AndreiS: serializing this field causes a NullPointerException when hashing a de-serialized
     * Variable (the variable has all fields set to null at the moment of hashing).
     *
     * dwightguth: made these volatile in order to simplify the code associated with computing
     * an entire tree of data all at once. if we want to eke out extra performance later, we can
     * adopt the same pattern used for hashCode, which is also safe and potentially a tiny bit faster.
     */
    volatile transient PSet<Variable> variableSet = null;
    volatile transient Boolean isGround = null;
    volatile transient Boolean isNormal = null;
    volatile transient Set<Term> userVariableSet = null;

    protected JavaSymbolicObject() {
        super();
    }

    protected JavaSymbolicObject(Source source, Location location) {
        super(location, source);
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * applying a substitution in (in a binder sensitive way) .
     */
    public T substituteWithBinders(
            Map<Variable, ? extends Term> substitution) {
        if (substitution.isEmpty() || isGround()) {
            return (T) this;
        }

        return (T) accept(new BinderSubstitutionTransformer(substitution));
    }

    /**
     * Returns a new {@code JavaSymbolicObject} instance obtained from this JavaSymbolicObject by
     * applying a substitution in (in a binder insensitive way) .
     */
    public T substitute(
            Map<Variable, ? extends Term> substitution) {
        if (substitution.isEmpty() || isGround()) {
            return (T) this;
        }

        return (T) accept(new SubstitutionTransformer(substitution));
    }

    /**
     * Returns a copy of this {@code JavaSymbolicObject} with each {@link Variable} renamed to a fresh name.
     */
    public T renameVariables() {
        return substitute(Variable.rename(variableSet()));
    }

    /**
     * Returns true if a call to {@link org.kframework.backend.java.kil.Term#substituteAndEvaluate(java.util.Map, TermContext)} may simplify this term.
     */
    public boolean canSubstituteAndEvaluate(Map<Variable, ? extends Term> substitution) {
        return (!substitution.isEmpty() && !isGround()) || !isNormal();
    }

    /**
     * Returns a lazily computed {@code Set} view of the variables in this
     * {@code JavaSymbolicObject}.
     */
    public PSet<Variable> variableSet() {
        if (variableSet == null) {
            if (isGround == null || !isGround) {
                new VariableSetFieldInitializer().visitNode(this);
            } else {
                variableSet = HashTreePSet.empty();
            }
        }
        return variableSet;
    }

    /**
     * Returns {@code true} if this JavaSymbolicObject does not contain any variables.
     */
    public boolean isGround() {
        if (isGround == null) {
            if (variableSet == null) {
                new IsGroundFieldInitializer().visitNode(this);
            } else {
                isGround = variableSet.isEmpty();
            }
        }
        return isGround;
    }

    /**
     * Returns true if this {@code JavaSymbolicObject} has no functions or
     * patterns, false otherwise.
     */
    public boolean isNormal() {
        if (isNormal == null) {
            new IsNormalFieldInitializer().visitNode(this);
        }
        return isNormal;
    }

    /**
     * Returns a {@code Set} view of the user variables (ie terms of sort Variable) in this
     * {@code JavaSymbolicObject}.
     * <p>
     * When the set of user variables has not been computed, this method will do the
     * computation.
     */
    public Set<Term> userVariableSet(GlobalContext global) {
        if (userVariableSet == null) {
            final Map<JavaSymbolicObject, Set<Term>> intermediate = new IdentityHashMap<>();
            IncrementalCollector<Term> visitor = new IncrementalCollector<>(
                    (set, term) -> term.userVariableSet = set,
                    term -> term.userVariableSet,
                    intermediate,
                    new LocalVisitor() {
                        @Override
                        public void visit(Term term) {
                            if (!(term instanceof KList) && global.getDefinition().subsorts().isSubsortedEq(Sort.VARIABLE, term.sort())) {
                                intermediate.get(term).add(term);
                            }
                        }
                    });
            accept(visitor);
            userVariableSet = visitor.getResultSet();
        }
        return Collections.unmodifiableSet(userVariableSet);
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }


    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        throw new UnsupportedOperationException();
    }

    // TODO(YilongL): remove the comments below to enforce that every subclass
    // has implemented the following two methods properly
    //@Override
    //public abstract boolean equals(Object object);

    //@Override
    //public abstract int hashCode();

}
