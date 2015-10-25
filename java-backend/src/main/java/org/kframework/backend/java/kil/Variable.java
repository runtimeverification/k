// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;


/**
 * A variable.
 *
 * @author AndreiS
 */
public class Variable extends Term implements Immutable, org.kframework.kore.KVariable {

    protected static final String VARIABLE_PREFIX = "_";
    protected static final AtomicInteger counter = new AtomicInteger(0);
    private static final Map<Pair<Integer, Sort>, Variable> deserializationAnonymousVariableMap = new ConcurrentHashMap<>();

    /**
     * Given a set of {@link Variable}s, returns a substitution that maps each
     * element inside to a fresh {@code Variable}.
     *
     * @param variableSet the set of {@code Variable}s
     * @return the substitution
     */
    public static BiMap<Variable, Variable> rename(Set<Variable> variableSet) {
        BiMap<Variable, Variable> substitution = HashBiMap.create(variableSet.size());
        for (Variable variable : variableSet) {
            substitution.put(variable, variable.getFreshCopy());
        }
        return substitution;
    }

    /**
     * Returns a fresh anonymous {@code Variable} of a given sort.
     *
     * @param sort the given sort
     * @return the fresh variable
     */
    public static Variable getAnonVariable(Sort sort) {
        return new Variable(VARIABLE_PREFIX + counter.getAndIncrement(), sort, true, -1);
    }

    /* TODO(AndreiS): cache the variables */
    private final String name;
    private final Sort sort;
    private final boolean anonymous;

    private final int ordinal;

    /**
     * @param name
     * @param sort
     * @param anonymous
     * @param ordinal   a unique index identifying the variable
     */
    public Variable(String name, Sort sort, boolean anonymous, int ordinal) {
        super(Kind.of(sort));

        assert name != null && sort != null;

        this.name = name;
        this.sort = sort;
        this.anonymous = anonymous;
        this.ordinal = ordinal;
    }

    public Variable(String name, Sort sort) {
        this(name, sort, false, -1);
    }

    public Variable(String name, Sort sort, int ordinal) {
        this(name, sort, false, ordinal);
    }

    public Variable(MetaVariable metaVariable) {
        this(metaVariable.variableName(), metaVariable.variableSort());
        this.copyAttributesFrom(metaVariable);
    }

    public Variable getFreshCopy() {
        Variable var = Variable.getAnonVariable(sort);
        var.copyAttributesFrom(this);
        return var;
    }

    /**
     * Returns a {@code String} representation of the name of this variable.
     */
    public String name() {
        return name;
    }

    public boolean isAnonymous() {
        return anonymous;
    }

    /**
     * @return the ordinal, a unique index indentifing the variable
     */
    public int ordinal() {
        return ordinal;
    }

    @Override
    public Sort sort() {
        return sort;
    }

    @Override
    public final boolean isExactSort() {
        return false;
    }

    @Override
    public final boolean isSymbolic() {
        return true;
    }

    public boolean unifyCollection(Collection collection) {
        return !(collection.concreteSize() != 0 && collection.collectionVariables().contains(this));
    }

    @Override
    public final boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Variable)) {
            return false;
        }

        Variable variable = (Variable) object;
        return name.equals(variable.name) && sort.equals(variable.sort);
    }

    @Override
    protected final int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Constants.HASH_PRIME + name.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + sort.hashCode();
        return hashCode;
    }

    @Override
    protected final boolean computeMutability() {
        return false;
    }

    @Override
    public String toString() {
        return name + ":" + sort;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    /**
     * Renames serialized anonymous variables to avoid name clashes with existing anonymous
     * variables.
     */
    Object readResolve() {
        if (anonymous) {
            int id = Integer.parseInt(name.substring(VARIABLE_PREFIX.length()));
            /* keep polling the counter until we acquire `id` successfully or we know that
            * `id` has been used and this anonymous variable must be renamed */
            for (int c = counter.get(); ; ) {
                if (id < c) {
                    return deserializationAnonymousVariableMap.computeIfAbsent(Pair.of(id, sort), p -> getFreshCopy());
                } else if (counter.compareAndSet(c, id + 1)) {
                    return this;
                }
            }
        } else {
            return this;
        }
    }

}
