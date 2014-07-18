// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;


/**
 * A meta representation of a variable.
 *
 * @see Variable
 *
 * @author: AndreiS
 */
public class MetaVariable extends Token {

    public static final Sort SORT = Sort.META_VARIABLE;

    private final String name;
    private final Sort sort;

    public MetaVariable(String name, Sort sort) {
        this.name = name;
        this.sort = sort;
    }

    public MetaVariable(Variable variable) {
        this(variable.name(), variable.sort());
    }

    @Override
    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this meta variable.
     */
    @Override
    public String value() {
        return name + ":" + sort;
    }

    /**
     * Returns a {@link Variable} with the meta representation given by this meta variable.
     */
    public Variable variable() {
        return new Variable(name, sort);
    }

    /**
     * Returns a {@code String} representation of the name of this meta variable.
     */
    public String variableName() {
        return name;
    }

    /**
     * Returns a {@code String} representation of the sort of this meta variable.
     */
    public Sort variableSort() {
        return sort;
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + name.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + sort.hashCode();
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof MetaVariable)) {
            return false;
        }

        MetaVariable metaVariable = (MetaVariable) object;
        return name.equals(metaVariable.name) && sort.equals(metaVariable.sort);
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

}
