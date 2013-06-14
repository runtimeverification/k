package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Utils;

import java.util.Collections;
import java.util.Set;


/**
 * A K term of the form {@code SORT(#"VALUE")}.
 *
 * @author AndreiS
 */
public abstract class Token extends Term implements Sorted {

    public Token() {
        super(Kind.KITEM);
    }

    /**
     * Returns a {@code String} representation of the sort of this token.
     */
    @Override
    public abstract String sort();

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this token.
     */
    public abstract String value();

    @Override
    public boolean isGround() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public Set<Variable> variableSet() {
        return Collections.emptySet();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + sort().hashCode();
        hash = hash * Utils.HASH_PRIME + value().hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Token)) {
            return false;
        }

        Token token = (Token) object;
        return sort().equals(token.sort()) && value().equals(token.value());
    }

    @Override
    public String toString() {
        return sort() + "(#\"" + value() + "\")";
    }

}
