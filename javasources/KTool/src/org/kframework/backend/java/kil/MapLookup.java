package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 *
 * @author AndreiS
 */
public class MapLookup extends Term {

    private final Term map;
    private final Term key;

    public MapLookup(Term map, Term key) {
        super(Kind.KITEM);
        this.map = map;
        this.key = key;
    }

    public Term evaluateLookup() {
        if (!(map instanceof BuiltinMap)) {
            return this;
        }

        Term value = ((BuiltinMap) map).get(key);
        if (value != null) {
            return value;
        } else if (map.isGround() && key.isGround() ) {
            return BoolToken.FALSE;
        } else {
            return this;
        }
    }

    public Term key() {
        return key;
    }

    public Term map() {
        return map;
    }

    @Override
    public boolean isSymbolic() {
        return true;
//        assert final : "isSymbolic is not supported by MapLookup (yet)";
//        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + key.hashCode();
        hash = hash * Utils.HASH_PRIME + map.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof MapLookup)) {
            return false;
        }

        MapLookup mapLookup = (MapLookup) object;
        return key.equals(mapLookup.key) && map.equals(mapLookup.map);
    }

    @Override
    public String toString() {
        return map.toString() + "[" + key + "]";
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
