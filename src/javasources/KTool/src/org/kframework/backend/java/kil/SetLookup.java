package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;

/**
 *
 * @author TraianSF
 */
public class SetLookup extends Term {

    private final Term base;
    private final Term key;

    public SetLookup(Term base, Term key) {
        super(Kind.KITEM);
        this.base = base;
        this.key = key;
    }

    public Term evaluateLookup() {
        if (!(base instanceof BuiltinSet)) {
            return this;
        }

        if (((BuiltinSet) base).contains(key)) {
            return BoolToken.TRUE;
        }
        return  this;
    }

    public Term key() {
        return key;
    }

    public Term base() {
        return base;
    }

    @Override
    public boolean isSymbolic() {
        return true;
//        assert false : "isSymbolic is not supported by SetLookup (yet)";
//        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + key.hashCode();
        hash = hash * Utils.HASH_PRIME + base.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof SetLookup)) {
            return false;
        }

        SetLookup mapLookup = (SetLookup) object;
        return key.equals(mapLookup.key) && base.equals(mapLookup.base);
    }

    @Override
    public String toString() {
        return base.toString() + "[" + key + "]";
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
