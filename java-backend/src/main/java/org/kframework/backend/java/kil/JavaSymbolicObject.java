// Copyright (c) 2013-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.symbolic.BinderSubstitutionTransformer;
import org.kframework.backend.java.symbolic.IncrementalCollector;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.backend.java.util.Constants;
import org.kframework.kore.K;
import org.pcollections.HashTreePSet;
import org.pcollections.PSet;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;


/**
 * Root of the Java Rewrite Engine internal representation class hierarchy.
 *
 * @author AndreiS
 */
public abstract class JavaSymbolicObject<T extends JavaSymbolicObject<T>>
        implements K, Transformable, Visitable {

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
    volatile transient Boolean isPure = null;
    volatile transient Set<Term> userVariableSet = null;

    private Att att;

    protected JavaSymbolicObject() {
        this(Att.empty());
    }

    protected JavaSymbolicObject(Source source, Location loc) {
        this(source, loc, Att.empty());
    }

    public JavaSymbolicObject(Source source, Location loc, Att att) {
        this(att.add(Location.class, loc).add(Source.class, source));
    }

    public JavaSymbolicObject(Att att) {
        this.att = att;
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
     * Returns true if this {@code JavaSymbolicObject} has no impure functions, false otherwise.
     * <p>
     * Impure functions return different results each time they are evaluated, thus their results cannot be cached.
     */
    public boolean isPure() {
        if (isPure == null) {
            new IsPureFieldInitializer().visitNode(this);
        }
        return isPure;
    }

    public boolean isConcrete() {
        return isGround() && isNormal();
    }

    public boolean isVariable() {
        return this instanceof Variable;
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
            @SuppressWarnings("unchecked")
            IncrementalCollector<Term> visitor = new IncrementalCollector<>(
                    (set, term) -> term.userVariableSet = set,
                    term -> term.userVariableSet,
                    intermediate,
                    new LocalVisitor() {
                        @Override
                        public void visit(Term term) {
                            if (!(term instanceof KList) && !(term instanceof KLabel) && global.getDefinition().subsorts().isSubsortedEq(Sort.KVARIABLE, term.sort())) {
                                intermediate.get(term).add(term);
                            }
                        }
                    });
            accept(visitor);
            userVariableSet = visitor.getResultSet();
        }
        return Collections.unmodifiableSet(userVariableSet);
    }

    public Att att() {
        return att;
    }

    public Optional<Source> source() {
        return this.att().getOptional(Source.class);
    }

    public Optional<Location> location() {
        return this.att().getOptional(Location.class);
    }

    public Source getSource() {
        return source().orElse(null);
    }

    public Location getLocation() {
        return location().orElse(null);
    }

    public void copyAttributesFrom(JavaSymbolicObject variable) {
        this.att.addAll(variable.att);
    }
    // TODO(YilongL): remove the comments below to enforce that every subclass
    // has implemented the following two methods properly
    //@Override
    //public abstract boolean equals(Object object);

    //@Override
    //public abstract int hashCode();


    public int computeHashCode() {
        throw new AssertionError("Subclasses should implement their own hashCode so this code should not be reachable");
    }

    public int cachedHashCode() {
        throw new AssertionError("Subclasses should implement their own hashCode so this code should not be reachable");
    }

    public void addAttribute(String key, String value) {
        att = att.add(key, value);
    }

    public void setAttributes(Att att) {
        this.att = att;
    }
}
