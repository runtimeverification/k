// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;
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
public class ListLookup extends Term implements DataStructureLookup {

    private final Term list;
    private final Term key;

    public ListLookup(Term list, Term key, Kind kind) {
        super(kind);
        this.list = list;
        this.key = key;
    }

    public Term evaluateLookup() {
        if (!(list instanceof BuiltinList)) {
            return this;
        }
        if (!(key instanceof IntToken)) {
            return this;
        }
        int index = ((IntToken) key).intValue();

        Term value = ((BuiltinList) list).get(index);
        return value;
    }

    public Term key() {
        return key;
    }

    public Term list() {
        return base();
    }
    
    @Override
    public Term base() {
        return list;
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
    public Type type() {
        return Type.LIST_LOOKUP;
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + key.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + list.hashCode();
        return hashCode;
    }
    
    @Override
    protected boolean computeHasCell() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ListLookup)) {
            return false;
        }

        ListLookup mapLookup = (ListLookup) object;
        return key.equals(mapLookup.key) && list.equals(mapLookup.list);
    }

    @Override
    public String toString() {
        return list.toString() + "[" + key + "]";
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
