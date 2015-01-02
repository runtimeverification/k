// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.Set;


/**
 * A K term of the form {@code SORT(#"VALUE")}.
 *
 * @author AndreiS
 */
public abstract class Token extends Term implements Immutable {

    public static Token of(Sort sort, String value) {
        if (sort.equals(BoolToken.SORT)) {
            return BoolToken.of(Boolean.parseBoolean(value));
        } else if (sort.equals(IntToken.SORT)) {
            return IntToken.of(value);
        } else if (sort.equals(FloatToken.SORT)) {
            return FloatToken.of(value);
        } else {
            return UninterpretedToken.of(sort, value);
        }
    }

    public Token() {
        super(Kind.KITEM);
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public abstract Sort sort();

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this token.
     */
    public abstract String value();

    @Override
    public final boolean isGround() {
        return true;
    }

    @Override
    public final boolean isSymbolic() {
        return false;
    }

    @Override
    public Set<Variable> variableSet() {
        return Collections.emptySet();
    }

    @Override
    protected final boolean computeMutability() {
        return false;
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
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public String toString() {
        return sort() + "(#\"" + value() + "\")";
    }

}
