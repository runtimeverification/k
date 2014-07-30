// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * Table of {@code public static} methods on builtin maps.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static Term constructor(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        return BuiltinMap.concatenate(map1, map2);
    }

    public static Term unit(TermContext context) {
        return BuiltinMap.EMPTY_MAP;
    }

    public static Term entry(Term key, Term value, TermContext context) {
        BuiltinMap.Builder builder = new BuiltinMap.Builder();
        builder.put(key, value);
        return builder.build();
    }

    public static Term lookup(BuiltinMap map, Term key, TermContext context) {
        MapLookup mapLookup = new MapLookup(map, key, Kind.KITEM);
        return mapLookup.evaluateLookup();
    }

    public static Term update(BuiltinMap map, Term key, Term value, TermContext context) {
        MapUpdate mapUpdate = new MapUpdate(
                map,
                Collections.<Term>emptySet(),
                Collections.singletonMap(key, value));
        return mapUpdate.evaluateUpdate();
    }

    public static Term remove(BuiltinMap map, Term key, TermContext context) {
        MapUpdate mapUpdate = new MapUpdate(
                map,
                Collections.singleton(key),
                Collections.<Term, Term>emptyMap());
        return mapUpdate.evaluateUpdate();
    }

    public static Term updateAll(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        BuiltinMap.Builder builder = new BuiltinMap.Builder();
        builder.concatenate(map1, map2);
        return builder.build();
    }

    public static BuiltinSet keys(BuiltinMap map, TermContext context) {
        if (!map.isConcreteCollection()) {
            return null;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(map.getEntries().keySet());
        return (BuiltinSet) builder.build();
    }

    public static BuiltinList values(BuiltinMap map, TermContext context) {
        if (!map.isConcreteCollection()) {
            return null;
        }

        List<Term> elements = new ArrayList<>(map.getEntries().values());
        return new BuiltinList(elements);
    }

    public static BoolToken inclusion(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        if (!map1.isGround() || !map2.isGround()) {
            return null;
        }

        return BoolToken.of(map2.getEntries().entrySet().containsAll(map1.getEntries().entrySet()));
    }
}
