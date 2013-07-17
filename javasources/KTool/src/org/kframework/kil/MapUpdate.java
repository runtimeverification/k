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

    /** {@code Map} of entries to be removed from the map */
    private final  Map<Term, Term> removeEntries;

    /** {@code Map} of entries to be updated in the map */
    private final Map<Term, Term> updateEntries;


    public MapUpdate(Variable map, Map<Term, Term> removeEntries, Map<Term, Term> updateEntries) {
        super(map.getSort());
        this.map = map;
        this.removeEntries = removeEntries;
        this.updateEntries = updateEntries;
    }

    public Variable map() {
        return map;
    }

    public Map<Term, Term> removeEntries() {
        return Collections.unmodifiableMap(removeEntries);
    }

    public Map<Term, Term> updateEntries(){
        return Collections.unmodifiableMap(updateEntries);
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + map.hashCode();
        hash = hash * Context.HASH_PRIME + removeEntries.hashCode();
        hash = hash * Context.HASH_PRIME + updateEntries.hashCode();
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
        return map.equals(mapUpdate.map) && removeEntries.equals(mapUpdate.removeEntries)
               && updateEntries.equals(mapUpdate.updateEntries);
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
