// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.*;

import org.kframework.backend.java.symbolic.*;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import org.kframework.kil.MapBuiltin;

/**
 *
 * @author AndreiS
 */
public class MapUpdate extends Term implements DataStructureUpdate {

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

    public Term evaluateUpdate(TermContext context) {
        if (removeSet.isEmpty() && updateMap().isEmpty()) {
            return map;
        }

        // TODO(AndreiS): hack to deal with maps with multiple patterns
        if (!BuiltinMapUtils.isNormalMap(map)) {
            return this;
        }
        BuiltinMap.Builder builder = BuiltinMap.builder();
        builder.putAll(BuiltinMapUtils.getMapEntries(map));

        List<Term> mapItems = new ArrayList<>();
        mapItems.addAll(BuiltinMapUtils.getMapPatterns(map));
        mapItems.addAll(BuiltinMapUtils.getMapVariables(map));

        Set<Term> pendingRemoveSet = new HashSet<>();
        for (Term key : removeSet) {
            if (builder.remove(key) == null) {
                pendingRemoveSet.add(key);
            }
        }

        if (!pendingRemoveSet.isEmpty()) {
            // TODO(YilongL): why not return Bottom when there is no frame
            if (!builder.getEntries().isEmpty()) {
                mapItems.add(builder.build());
            }
            return new MapUpdate(
                    BuiltinMap.concatenationMap(mapItems, context),
                    pendingRemoveSet,
                    updateMap);
        }

        builder.putAll(updateMap);
        if (!builder.getEntries().isEmpty()) {
            mapItems.add(builder.build());
        }
        return BuiltinMap.concatenationMap(mapItems, context);
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
    public int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + map.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + removeSet.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + updateMap.hashCode();
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
