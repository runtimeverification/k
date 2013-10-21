package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 *
 * @author AndreiS
 */
public class ListLookup extends Term {

    private final Term list;
    private final Term key;

    public ListLookup(Term list, Term key) {
        super(Kind.KITEM);
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
        return list;
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
        hash = hash * Utils.HASH_PRIME + list.hashCode();
        return hash;
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
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
