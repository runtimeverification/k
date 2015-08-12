// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kore.KToken;
import org.kframework.utils.StringUtil;


/**
 * A K term of the form {@code SORT(#"VALUE")}.
 *
 * @author AndreiS
 */
public abstract class Token extends Term implements KoreRepresentation, Immutable, KToken {

    public static Token of(Sort sort, String value) {
        if (sort.equals(BoolToken.SORT)) {
            return BoolToken.of(Boolean.parseBoolean(value));
        } else if (sort.equals(IntToken.SORT)) {
            return IntToken.of(value);
        } else if (sort.equals(FloatToken.SORT)) {
            return FloatToken.of(value);
        } else if (sort.equals(StringToken.SORT)) {
            return StringToken.of(StringUtil.unquoteKString(value));
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

    @Override
    public String s() {
        return value();
    }

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
    protected final boolean computeMutability() {
        return false;
    }

    @Override
    public Token toKore() {
        return this;
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
