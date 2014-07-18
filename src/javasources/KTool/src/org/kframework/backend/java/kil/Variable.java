// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;


/**
 * A variable.
 *
 * @author AndreiS
 */
public class Variable extends Term implements Immutable {

    protected static final String VARIABLE_PREFIX = "_";
    protected static int counter = 0;
    private static Map<Integer, Variable> deserializationAnonymousVariableMap = new HashMap<>();

    /**
     * Given a set of {@link Variable}s, returns a substitution that maps each
     * element inside to a fresh {@code Variable}.
     *
     * @param variableSet
     *            the set of {@code Variable}s
     * @return the substitution
     */
    public static Map<Variable, Variable> getFreshSubstitution(Set<Variable> variableSet) {
        Map<Variable, Variable> substitution = new HashMap<Variable, Variable>();
        for (Variable variable : variableSet) {
            substitution.put(variable, variable.getFreshCopy());
        }
        return substitution;
    }

    /**
     * Returns a fresh {@code Variable} of a given sort.
     *
     * @param sort
     *            the given sort
     * @return the fresh variable
     */
    public static Variable getFreshVariable(Sort sort) {
        return new Variable(VARIABLE_PREFIX + (counter++), sort, true);
    }

    /* TODO(AndreiS): cache the variables */
    private final String name;
    private final Sort sort;
    private final boolean anonymous;

    public Variable(String name, Sort sort, boolean anonymous) {
        super(Kind.of(sort));

        assert name != null && sort != null;

        this.name = name;
        this.sort = sort;
        this.anonymous = anonymous;
    }

    public Variable(String name, Sort sort) {
        this(name, sort, false);
    }

    public Variable(MetaVariable metaVariable) {
        this(metaVariable.variableName(), metaVariable.variableSort());
    }

    public Variable getFreshCopy() {
        return Variable.getFreshVariable(sort);
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
        hashCode = hashCode * Utils.HASH_PRIME + name.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + sort.hashCode();
        return hashCode;
    }

    @Override
    protected final boolean computeHasCell() {
        return false;
    }

    @Override
    public String toString() {
        return name + ":" + sort;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
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
            if (id < counter) {
                Variable variable = deserializationAnonymousVariableMap.get(id);
                if (variable == null) {
                    variable = getFreshCopy();
                    deserializationAnonymousVariableMap.put(id, variable);
                }
                return variable;
            } else {
                counter = id + 1;
                return this;
            }
        } else {
            return this;
        }
    }

}
