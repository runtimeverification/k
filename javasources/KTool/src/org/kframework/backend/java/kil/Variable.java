package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 *
 *
 * @author AndreiS
 */
public class Variable extends Term implements Sorted {

    /* TODO(AndreiS): cache the varibles */
    protected final String name;
    protected final String sort;

    public Variable(String name, String sort) {
        super(Kind.of(sort));
        this.name = name;
        this.sort = sort;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

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
