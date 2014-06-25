// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BuiltinMapUtils;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

/**
 *
 * @author AndreiS
 */
public class MapLookup extends Term implements DataStructureLookup {

    private final Term map;
    private final Term key;

    public MapLookup(Term map, Term key, Kind kind) {
        super(kind);
        this.map = map;
        this.key = key;
    }

    public Term evaluateLookup() {
        // TODO(AndreiS): hack to deal with maps with multiple patterns
        if (map instanceof KItem) {
            Term result = BuiltinMapUtils.getMapEntries(map).get(key);
            if (result != null) {
                return result;
            }
        }

        if (!(map instanceof BuiltinMap)) {
            return this;
        }

        Term value = ((BuiltinMap) map).get(key);
        if (value != null) {
            return value;
        } else if (map.isGround() && key.isGround()) {
            return new Bottom(kind);
        } else if (((BuiltinMap) map).isEmpty()) {
            return new Bottom(kind);
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
    public boolean isExactSort() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return true;
//        assert final : "isSymbolic is not supported by MapLookup (yet)";
//        throw new UnsupportedOperationException();
    }

    @Override
    public String sort() {
        return kind.toString();
    }

    @Override
    public int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + key.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + map.hashCode();
        return hashCode;
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
    public void accept(Matcher matcher, Term pattern) {
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
