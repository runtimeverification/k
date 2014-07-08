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

import java.util.*;

import com.google.common.base.Preconditions;


/**
 * Table of {@code public static} methods on builtin maps.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static Term construct(BuiltinMap map1, BuiltinMap map2, TermContext context) {
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
        return mapUpdate.evaluateUpdate(context);
    }

    public static Term remove(BuiltinMap map, Term key, TermContext context) {
        MapUpdate mapUpdate = new MapUpdate(
                map,
                Collections.singleton(key),
                Collections.<Term, Term>emptyMap());
        return mapUpdate.evaluateUpdate(context);
    }

    public static Term updateAll(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        BuiltinMap.Builder builder = new BuiltinMap.Builder();
        builder.concatenate(map1, map2);
        return builder.build();
    }

    public static BuiltinSet keys(BuiltinMap map, TermContext context) {
        Preconditions.checkArgument(!map.hasFrame(), "argument " + map + " has frame");

        Set<Term> elements = new HashSet<>(map.getEntries().keySet());
        return new BuiltinSet(elements);
    }

    public static BuiltinList values(BuiltinMap map, TermContext context) {
        Preconditions.checkArgument(!map.hasFrame(), "argument " + map + " has frame");

        List<Term> elements = new ArrayList<>(map.getEntries().values());
        return new BuiltinList(elements);
    }

    public static BoolToken inclusion(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        Preconditions.checkArgument(!map1.hasFrame(), "argument " + map1 + " has frame");

        for (Map.Entry<Term, Term> entry : map1.getEntries().entrySet()) {
            if (!entry.getValue().equals(map2.get(entry.getKey()))) {
                return BoolToken.FALSE;
            }
        }

        return BoolToken.TRUE;
    }
}
