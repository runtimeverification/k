// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import com.google.common.collect.MapDifference;
import com.google.common.collect.MapDifference.ValueDifference;
import com.google.common.collect.Maps;
import com.google.common.collect.Multisets;

import org.kframework.backend.java.kil.*;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Table of {@code public static} methods on builtin maps.
 *
 * @author AndreiS
 */
public class BuiltinMapOperations {

    public static Term constructor(Term map1, Term map2, TermContext context) {
        if (map1.sort() != Sort.MAP || map2.sort() != Sort.MAP) {
            throw new IllegalArgumentException();
        }
        return BuiltinMap.concatenate(context.global(), map1, map2);
    }

    public static Term unit(TermContext context) {
        return BuiltinMap.builder(context.global()).build();
    }

    public static Term entry(Term key, Term value, TermContext context) {
        BuiltinMap.Builder builder = new BuiltinMap.Builder(context.global());
        builder.put(key, value);
        return builder.build();
    }

    public static Term lookup(Term map, Term key, TermContext context) {
        while (DataStructures.isMapUpdate(map)) {
            Term value = builtinMapLookup(DataStructures.getMapUpdateMap(map), key);
            if (!(value instanceof Bottom)) {
                return value;
            }
            map = DataStructures.getMapUpdateBase(map);
        }

        return builtinMapLookup(map, key);
    }

    public static Term builtinMapLookup(Term map, Term key) {
        if (!(map instanceof BuiltinMap)) {
            return null;
        }
        BuiltinMap builtinMap = (BuiltinMap) map;


        Term value = builtinMap.get(key);
        if (value != null) {
            return value;
        } else if (key.isGround() && builtinMap.isConcreteCollection() && builtinMap.hasOnlyGroundKeys()) {
            return Bottom.BOTTOM;
        } else if (builtinMap.isEmpty()) {
            return Bottom.BOTTOM;
        } else {
            return null;
        }
    }

    public static Term update(Term map, Term key, Term value, TermContext context) {
        BuiltinMap.Builder builder = BuiltinMap.builder(context.global());
        builder.put(key, value);
        return updateAll(map, (BuiltinMap) builder.build(), context);
    }

    public static Term remove(Term map, Term key, TermContext context) {
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.add(key);
        return removeAll(map, (BuiltinSet) builder.build(), context);
    }

    public static Term difference(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        BuiltinMap.Builder builder = BuiltinMap.builder(context.global());
        if (!map1.isGround() || !map2.isGround()) {
            if (map1.getEntries().entrySet().containsAll(map2.getEntries().entrySet())
                    && Multisets.containsOccurrences(map1.baseTerms(), map2.baseTerms())) {
                builder.putAll(Maps.difference(map1.getEntries(), map2.getEntries()).entriesOnlyOnLeft());
                builder.concatenate(Multisets.difference(map1.baseTerms(), map2.baseTerms()));
                return builder.build();
            } else {
                return null;
            }
        } else {
            /* Maps.difference breaks down the Venn diagram into four parts, see:
             * http://code.google.com/p/guava-libraries/wiki/CollectionUtilitiesExplained#difference */
            MapDifference<Term, Term> mapDiff = Maps.difference(map1.getEntries(), map2.getEntries());
            builder.putAll(mapDiff.entriesOnlyOnLeft());
            for (Entry<Term, ValueDifference<Term>> e : mapDiff.entriesDiffering().entrySet()) {
                builder.put(e.getKey(), e.getValue().leftValue());
            }
            return builder.build();
        }
    }

    public static Term updateAll(Term map, BuiltinMap updateBuiltinMap, TermContext context) {
        if (!updateBuiltinMap.isConcreteCollection()) {
            return null;
        }

        if (updateBuiltinMap.isEmpty()) {
            return map;
        }

        if (!(map instanceof BuiltinMap)) {
            return null;
        }
        BuiltinMap builtinMap = (BuiltinMap) map;

        BuiltinMap.Builder builder = new BuiltinMap.Builder(context.global());
        builder.update(builtinMap, updateBuiltinMap);
        BuiltinMap updatedMap = (BuiltinMap) builder.build();
        if (builtinMap.isConcreteCollection()
                || updatedMap.concreteSize() == builtinMap.concreteSize()) {
            return updatedMap;
        } else {
            return null;
        }
    }

    public static Term removeAll(Term map, BuiltinSet removeBuiltinSet, TermContext context) {
        if (!removeBuiltinSet.isConcreteCollection()) {
            return null;
        }

        if (removeBuiltinSet.isEmpty()) {
            return map;
        }

        if (!(map instanceof BuiltinMap)) {
            return null;
        }
        BuiltinMap builtinMap = (BuiltinMap) map;

        BuiltinMap.Builder builder = BuiltinMap.builder(context.global());
        builder.concatenate(builtinMap);

        Set<Term> pendingRemoveSet = removeBuiltinSet.elements().stream()
                .filter(element -> builder.remove(element) == null)
                .collect(Collectors.toSet());

        if (!builtinMap.isConcreteCollection() && !pendingRemoveSet.isEmpty()) {
            return DataStructures.mapRemoveAll(builder.build(), pendingRemoveSet, context);
        } else {
            return builder.build();
        }
    }

    public static BuiltinSet keys(BuiltinMap map, TermContext context) {
        if (map.getEntries().isEmpty() && !map.isEmpty()) {
            return null;
        }
        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(map.getEntries().keySet());
        if (!map.isConcreteCollection()) {
            builder.add(KItem.of(
                    KLabelConstant.of("'keys", context.definition()),
                    KList.concatenate(BuiltinMap.concatenate(context.global(), map.baseTerms())),
                    context.global()));
        }
        return (BuiltinSet) builder.build();
    }

    public static BuiltinList values(BuiltinMap map, TermContext context) {
        if (!map.isConcreteCollection()) {
            return null;
        }

        List<Term> elements = new ArrayList<>(map.getEntries().values());
        BuiltinList.Builder builder = BuiltinList.builder(context.global());
        builder.addItems(elements);
        return (BuiltinList) builder.build();
    }

    public static BoolToken inclusion(BuiltinMap map1, BuiltinMap map2, TermContext context) {
        if (!map1.isGround() || !map2.isGround()) {
            return null;
        }

        return BoolToken.of(map2.getEntries().entrySet().containsAll(map1.getEntries().entrySet()));
    }

    public static Term choice(BuiltinMap map, TermContext context) {
        if (!map.getEntries().isEmpty()) {
            return map.getEntries().keySet().iterator().next();
        } else if (map.isEmpty()) {
            return Bottom.BOTTOM;
        } else {
            return null;
        }
    }

}
