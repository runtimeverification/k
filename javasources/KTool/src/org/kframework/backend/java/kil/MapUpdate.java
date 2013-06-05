package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

/**
 *
 * @author AndreiS
 */
public class MapUpdate extends Term {

    /** {@link Term} representation of the map */
    private final Term map;
    /** {@code Set} of keys to be removed from the map */
    private final Set<Term> removeSet;
    /** {@code Map} of entries to be updated in the map */
    private final Map<Term, Term> updateMap;

    public MapUpdate(Term map, Set<Term> removeSet, Map<Term, Term> updateMap) {
        super(Kind.MAP);
        this.map = map;
        this.removeSet = removeSet;
        this.updateMap = updateMap;
    }

    public Term map() {
        return map;
    }

    public Set<Term> removeSet() {
        return Collections.unmodifiableSet(removeSet);
    }

    public Map<Term, Term> updateMap(){
        return Collections.unmodifiableMap(updateMap);
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + map.hashCode();
        hash = hash * Utils.HASH_PRIME + removeSet.hashCode();
        hash = hash * Utils.HASH_PRIME + updateMap.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof MapUpdate)) {
            return false;
        }

        MapUpdate mapUpdate = (MapUpdate) object;
        return map.equals(mapUpdate.map) && removeSet.equals(mapUpdate.removeSet)
               && updateMap.equals(mapUpdate.updateMap);
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
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
