package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.*;

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
        super(Kind.KITEM);
        this.map = map;
        this.removeSet = new HashSet<Term>(removeSet);
        this.updateMap = updateMap;
    }

    public Term evaluateUpdate() {
        if (removeSet.isEmpty() && updateMap().isEmpty()) {
            return map;
        }

        if (!(map instanceof BuiltinMap)) {
            return this;
        }

        BuiltinMap builtinMap = ((BuiltinMap) map);

        Map<Term, Term> entries = new HashMap<Term, Term>(builtinMap.getEntries());
        for (Iterator<Term> iterator = removeSet.iterator(); iterator.hasNext();) {
            if (entries.remove(iterator.next()) != null) {
                iterator.remove();
            }
        }

        if (!removeSet.isEmpty()) {
            return new MapUpdate(builtinMap, removeSet, updateMap);
        }

        entries.putAll(updateMap);

        if (builtinMap.hasFrame()) {
            return new BuiltinMap(entries, builtinMap.frame());
        } else {
            return new BuiltinMap(entries);
        }
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
        return false;
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
    public String toString() {
        String s = map.toString();
        for (Term key : removeSet) {
            s += "[" + key + " <- undef]";
        }
        for (Map.Entry<Term, Term> entry : updateMap.entrySet()) {
            s += "[" + entry.getKey() + " <- " + entry.getValue() + "]";
        }
        return s;
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
