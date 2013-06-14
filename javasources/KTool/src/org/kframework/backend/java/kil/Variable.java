package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;


/**
 * A variable.
 *
 * @author AndreiS
 */
public class Variable extends Term implements Sorted {

    /* TODO(AndreiS): cache the variables */
    protected final String name;
    protected final String sort;

    public Variable(String name, String sort) {
        super(Kind.of(sort));
        this.name = name;
        this.sort = sort;
    }

    public Variable(MetaVariable metaVariable) {
        this(metaVariable.variableName(), metaVariable.variableSort());
    }

    public static Map<Variable, Variable> getFreshSubstitution(Set<Variable> variableSet) {
        Map<Variable, Variable> substitution = new HashMap<Variable, Variable>();
        for (Variable variable : variableSet) {
            substitution.put(variable, AnonymousVariable.getFreshVariable(variable.sort()));
        }
        return substitution;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    /**
     * Returns a {@code String} representation of the name of this variable.
     */
    public String name() {
        return name;
    }

    /**
     * Returns a {@code String} representation of the sort of this variable.
     */
    @Override
    public String sort() {
        return sort;
    }

	@Override
	public boolean equals(Object object) {
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
	public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + name.hashCode();
        hash = hash * Utils.HASH_PRIME + sort.hashCode();
		return hash;
	}

    @Override
    public String toString() {
        return name + ":" + sort;
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
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
