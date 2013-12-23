package org.kframework.backend.java.kil;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KSorts;
import org.kframework.krun.K;

/**
 *
 * @author AndreiS
 */
public class MapLookup extends Term {

    private final Term map;
    private final Term key;

    public MapLookup(Term map, Term key, Kind kind) {
        super(kind);
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
        } else if (K.do_testgen && map.isGround() && key instanceof Variable) {
            // TODO(YilongL): get rid of the tag K.do_testgen later
            value = Variable.getFreshVariable(KSorts.K);
            List<UninterpretedConstraint> multiConstraints = new ArrayList<UninterpretedConstraint>();
            /* perform narrowing on the key according to the keys of the map */
            for (Term k : ((BuiltinMap) map).getEntries().keySet()) {
                UninterpretedConstraint cnstr = new UninterpretedConstraint();
                cnstr.add(key, k);
                cnstr.add(value, ((BuiltinMap) map).get(k));
                multiConstraints.add(cnstr);
            }
            return new TermFormulaPair(value, multiConstraints);
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
