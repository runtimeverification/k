package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
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

    protected static final String VARIABLE_PREFIX = "__var__";
    protected static int counter = 0;
    private static Map<Integer, Variable> deserializationAnonymousVariableMap = new HashMap<>();

    public static Map<Variable, Variable> getFreshSubstitution(Set<Variable> variableSet) {
        Map<Variable, Variable> substitution = new HashMap<Variable, Variable>();
        for (Variable variable : variableSet) {
            substitution.put(variable, variable.getFreshCopy());
        }
        return substitution;
    }

    public static Variable getFreshVariable(String sort) {
        return new Variable(VARIABLE_PREFIX + (counter++), sort, true);
    }
    
    /* TODO(AndreiS): cache the variables */
    private final String name;
    private final String sort;
    private final boolean anonymous;

    public Variable(String name, String sort, boolean anonymous) {
        super(Kind.of(sort));

        assert name != null && sort != null;

        this.name = name;
        this.sort = sort;
        this.anonymous = anonymous;
    }

    public Variable(String name, String sort) {
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

    /**
     * Returns a {@code String} representation of the sort of this variable.
     */
    @Override
    public String sort() {
        return sort;
    }

    @Override
    public boolean isSymbolic() {
        return true;
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
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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
    private Object readResolve() {
        if (anonymous) {
            int id = Integer.parseInt(name.substring(VARIABLE_PREFIX.length()));
            if (id < counter) {
                Variable variable = deserializationAnonymousVariableMap.get(id);
                if (variable == null) {
                    variable = getFreshVariable(sort);
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
