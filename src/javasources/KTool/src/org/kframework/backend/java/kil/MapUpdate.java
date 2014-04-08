package org.kframework.backend.java.kil;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;

/**
 *
 * @author AndreiS
 */
public class MapUpdate extends Term {

    /** {@link Term} representation of the map */
    private final Term map;
    /** {@code Set} of keys to be removed from the map */
    private final ImmutableSet<Term> removeSet;
    /** {@code Map} of entries to be updated in the map */
    private final ImmutableMap<Term, Term> updateMap;

    public MapUpdate(Term map, Set<Term> removeSet, Map<Term, Term> updateMap) {
        super(Kind.KITEM);
        this.map = map;
        this.removeSet = ImmutableSet.copyOf(removeSet);
        this.updateMap = ImmutableMap.copyOf(updateMap);
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
        Set<Term> keysToRemove = new HashSet<Term>();
        for (Iterator<Term> iterator = removeSet.iterator(); iterator.hasNext();) {
            Term nextKey = iterator.next();
            if (entries.remove(nextKey) != null) {
                keysToRemove.add(nextKey);
            }
        }

        if (removeSet.size() > keysToRemove.size()) {
            return new MapUpdate(builtinMap, Sets.difference(removeSet, keysToRemove), updateMap);
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

    public ImmutableSet<Term> removeSet() {
        return removeSet;
    }

    public ImmutableMap<Term, Term> updateMap(){
        return updateMap;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        // TODO(YilongL): throw an exception instead?
        return false;
    }

    @Override
    public String sort() {
        return map.sort();
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + map.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + removeSet.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + updateMap.hashCode();
        }
        return hashCode;
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
    public void accept(Unifier unifier, Term pattern) {
        // TODO(YilongL): throw an exception instead?
        unifier.unify(this, pattern);
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
