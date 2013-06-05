package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collections;
import java.util.Set;
import java.util.Map;


/**
 * Builtin map update operation.
 *
 * @author AndreiS
 */
public class MapUpdate extends Term {

    /** {@link Variable} name of the map */
    private final Variable map;

    /** {@code Set} of keys to be removed from the map */
    private final Set<Term> removeSet;

    /** {@code Map} of entries to be updated in the map */
    private final Map<Term, Term> updateMap;


    public MapUpdate(Variable map, Set<Term> removeSet, Map<Term, Term> updateMap) {
        super(map.getSort());
        this.map = map;
        this.removeSet = removeSet;
        this.updateMap = updateMap;
    }

    public Variable map() {
        return map;
    }

    public Set<Term> removeSet() {
        return Collections.unmodifiableSet(removeSet);
    }

    public Map<Term, Term> updateMap(){
        return Collections.unmodifiableMap(updateMap);
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + map.hashCode();
        hash = hash * Context.HASH_PRIME + removeSet.hashCode();
        hash = hash * Context.HASH_PRIME + updateMap.hashCode();
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
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
