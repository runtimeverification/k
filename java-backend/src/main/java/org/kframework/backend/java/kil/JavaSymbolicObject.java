// Copyright (c) 2013-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BinderSubstitutionTransformer;
import org.kframework.backend.java.symbolic.IncrementalCollector;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.visitors.Visitor;

import java.io.Serializable;
import java.util.Collections;
import java.util.IdentityHashMap;
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
     * Field used for caching the hash code
     */
    protected transient int hashCode = Utils.NO_HASHCODE;

    /**
     * AndreiS: serializing this field causes a NullPointerException when hashing a de-serialized
     * Variable (the variable has all fields set to null at the moment of hashing).
     *
     * dwightguth: made these volatile in order to simplify the code associated with computing
     * an entire tree of data all at once. if we want to eke out extra performance later, we can
     * adopt the same pattern used for hashCode, which is also safe and potentially a tiny bit faster.
     */
    volatile transient Set<Variable> variableSet = null;
    volatile transient Set<Term> userVariableSet = null;
    volatile transient Set<Term> functionKLabels = null;

    protected JavaSymbolicObject() {
        super();
    }

    protected JavaSymbolicObject(Source source, Location location) {
        super(location, source);
    }

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
     * Returns true if a call to {@link org.kframework.backend.java.kil.Term#substituteAndEvaluate(java.util.Map, TermContext)} may simplify this term.
     */
    public boolean canSubstituteAndEvaluate(Map<Variable, ? extends Term> substitution) {
        return (!substitution.isEmpty() && !isGround()) || !isNormal();
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
            final Map<JavaSymbolicObject, Set<Variable>> intermediate = new IdentityHashMap<>();
            IncrementalCollector<Variable> visitor = new IncrementalCollector<>(
                    (set, term) -> term.variableSet = set,
                    term -> term.variableSet,
                    intermediate,
                    new LocalVisitor() {
                        @Override
                        public void visit(Variable variable) {
                            intermediate.get(variable).add(variable);
                        }
                    });
            accept(visitor);
            variableSet = visitor.getResultSet();
        }
        return Collections.unmodifiableSet(variableSet);
    }

     /**
     * Returns a {@code Set} view of the user variables (ie terms of sort Variable) in this
     * {@code JavaSymbolicObject}.
     * <p>
     * When the set of user variables has not been computed, this method will do the
     * computation instead of simply returning {@code null}
     * {@link JavaSymbolicObject#getUserVariableSet()}.
     */
    public Set<Term> userVariableSet(TermContext context) {
        if (userVariableSet == null) {
            final Map<JavaSymbolicObject, Set<Term>> intermediate = new IdentityHashMap<>();
            IncrementalCollector<Term> visitor = new IncrementalCollector<>(
                    (set, term) -> term.userVariableSet = set,
                    term -> term.userVariableSet,
                    intermediate,
                    new LocalVisitor() {
                        @Override
                        public void visit(Term term) {
                            if (context.definition().subsorts().isSubsortedEq(Sort.VARIABLE, term.sort())) {
                                intermediate.get(term).add(term);
                            }
                        }
                    });
            accept(visitor);
            userVariableSet = visitor.getResultSet();
        }
        return Collections.unmodifiableSet(userVariableSet);
    }



    /**
     * Returns true if this {@code JavaSymbolicObject} has no functions or
     * patterns, false otherwise.
     * <p>
     * When the set of variables has not been computed, this method will do the
     * computation instead of simply returning {@code null}.
     */
    public boolean isNormal() {
        if (functionKLabels == null) {
            final Map<JavaSymbolicObject, Set<Term>> intermediate = new IdentityHashMap<>();
            IncrementalCollector<Term> visitor = new IncrementalCollector<>(
                    (set, term) -> term.functionKLabels = set,
                    term -> term.functionKLabels,
                    intermediate,
                    new LocalVisitor() {
                        @Override
                        public void visit(KItem kItem) {
                            if (kItem.isSymbolic()) {
                                intermediate.get(kItem).add(kItem.kLabel());
                            }
                        }

                        @Override
                        public void visit(KItemProjection projection) {
                            intermediate.get(projection).add(projection);
                        }
                    });
            accept(visitor);
            functionKLabels = visitor.getResultSet();
        }
        return functionKLabels.size() == 0;
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
     * Gets the cached set of variables in this {@code JavaSymbolicObject}.
     *
     * @return a set of variables in this {@code JavaSymbolicObject} if they
     *         have been computed; otherwise, {@code null}
     * @see JavaSymbolicObject#variableSet()
     */
    public Set<Variable> getVariableSet() {
        return variableSet;
    }

    /**
     * Gets the cached set of variables in this {@code JavaSymbolicObject}.
     *
     * @return a set of variables in this {@code JavaSymbolicObject} if they
     *         have been computed; otherwise, {@code null}
     * @see JavaSymbolicObject#variableSet()
     */
    public Set<Term> getUserVariableSet() {
        return userVariableSet;
    }

    // TODO(YilongL): remove the comments below to enforce that every subclass
    // has implemented the following two methods properly
    //@Override
    //public abstract boolean equals(Object object);

    //@Override
    //public abstract int hashCode();

}
