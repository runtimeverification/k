// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;

import java.util.Map;
import java.util.Set;


/**
 * Contains helper methods for handling data structures and operations (lookup, update, ...) on data structures.
 *
 * TODO: make these methods take GlobalContext instead of TermContext as argument
 *
 * @author AndreiS
 */
public interface DataStructures {

    String MAP_CHOICE = "Map:choice";
    String SET_CHOICE = "Set:choice";
    String LIST_GET = "List:get";
    String MAP_LOOKUP = "Map:lookup";
    String SET_MEMBERSHIP = "Set:in";
    String LIST_RANGE = "List:range";
    String MAP_UPDATE = "'updateMap";
    String MAP_REMOVE_ALL = "'removeAll";
    String SET_REMOVE_ALL = "Set:difference";

    static KItem lookup(Term base, Term key, TermContext context) {
        KLabelConstant klabel;
        KList kList;
        if (base.sort().equals(Sort.LIST)) {
            klabel = KLabelConstant.of(LIST_GET, context.definition());
            kList = (KList) KList.concatenate(base, key);
        } else if (base.sort().equals(Sort.MAP)) {
            klabel = KLabelConstant.of(MAP_LOOKUP, context.definition());
            kList = (KList) KList.concatenate(base, key);
        } else if (base.sort().equals(Sort.SET)) {
            klabel = KLabelConstant.of(SET_MEMBERSHIP, context.definition());
            kList = (KList) KList.concatenate(key, base);
        } else {
            assert false : "unimplemented missing case";
            return null;
        }
        return KItem.of(klabel, kList, context.global(), base.getSource(), base.getLocation());
    }

    static boolean isChoice(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && (((KItem) term).kLabel().toString().equals(MAP_CHOICE)
                        || ((KItem) term).kLabel().toString().equals(SET_CHOICE))
                && ((KItem) term).kList() instanceof KList
                && ((KList) ((KItem) term).kList()).isConcreteCollection()
                && ((KList) ((KItem) term).kList()).concreteSize() == 1;
    }

    static boolean isLookup(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && (((KItem) term).kLabel().toString().equals(LIST_GET)
                        || ((KItem) term).kLabel().toString().equals(MAP_LOOKUP)
                        || ((KItem) term).kLabel().toString().equals(SET_MEMBERSHIP))
                && ((KItem) term).kList() instanceof KList
                && ((KList) ((KItem) term).kList()).isConcreteCollection()
                && ((KList) ((KItem) term).kList()).concreteSize() == 2;
    }

    static boolean isLookupOrChoice(Term term) {
        return isLookup(term) || isChoice(term);
    }

    static Term getLookupBase(Term term) {
        assert isLookup(term);
        return !term.sort().equals(Sort.SET) ?
               ((KList) (((KItem) term).kList())).get(0) :
               ((KList) (((KItem) term).kList())).get(1);

    }

    static Term getLookupKey(Term term) {
        assert isLookup(term);
        return !term.sort().equals(Sort.SET) ?
               ((KList) (((KItem) term).kList())).get(1) :
               ((KList) (((KItem) term).kList())).get(0);

    }

    static KItem choice(Term base, TermContext context) {
        KLabelConstant klabel;
        if (base.sort().equals(Sort.MAP)) {
            klabel = KLabelConstant.of(MAP_CHOICE, context.definition());
        } else if (base.sort().equals(Sort.SET)) {
            klabel = KLabelConstant.of(SET_CHOICE, context.definition());
        } else {
            assert false : "unimplemented missing case";
            return null;
        }
        return KItem.of(klabel, KList.singleton(base), context.global(), base.getSource(), base.getLocation());
    }

    static Term listRange(Term base, int removeLeft, int removeRight, TermContext context) {
        if (removeLeft == 0 && removeRight == 0) {
            return base;
        }

        return KItem.of(
                KLabelConstant.of(LIST_RANGE, context.definition()),
                KList.concatenate(base, IntToken.of(removeLeft), IntToken.of(removeRight)),
                context.global(), base.getSource(), base.getLocation());
    }

    static Term mapRemoveAll(Term base, Set<Term> removeSet, TermContext context) {
        if (removeSet.isEmpty()) {
            return base;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(removeSet);
        return KItem.of(
                KLabelConstant.of(MAP_REMOVE_ALL, context.definition()),
                KList.concatenate(base, builder.build()),
                context.global(), base.getSource(), base.getLocation());
    }

    static Term mapUpdateAll(Term base, Map<Term, Term> updateMap, TermContext context) {
        if (updateMap.isEmpty()) {
            return base;
        }

        BuiltinMap.Builder builder = new BuiltinMap.Builder(context.global());
        builder.putAll(updateMap);
        return KItem.of(
                KLabelConstant.of(MAP_UPDATE, context.definition()),
                KList.concatenate(base, builder.build()),
                context.global(), base.getSource(), base.getLocation());
    }

    static Term setDifference(Term base, Set<Term> removeSet, TermContext context) {
        if (removeSet.isEmpty()) {
            return base;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder(context.global());
        builder.addAll(removeSet);
        return KItem.of(
                KLabelConstant.of(SET_REMOVE_ALL, context.definition()),
                KList.concatenate(base, builder.build()),
                context.global(), base.getSource(), base.getLocation());
    }

    static boolean isMapUpdate(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && ((KItem) term).kLabel().toString().equals(MAP_UPDATE)
                && ((KItem) term).kList() instanceof KList
                && ((KList) ((KItem) term).kList()).isConcreteCollection()
                && ((KList) ((KItem) term).kList()).concreteSize() == 2;
    }

    static Term getMapUpdateBase(Term term) {
        assert isMapUpdate(term);
        return ((KList) (((KItem) term).kList())).get(0);

    }

    static Term getMapUpdateMap(Term term) {
        assert isMapUpdate(term);
        return ((KList) (((KItem) term).kList())).get(1);
    }

    static CellCollection.Cell getCellEntry(Term term) {
        assert term instanceof CellCollection
               && ((CellCollection) term).isConcreteCollection()
               && ((CellCollection) term).concreteSize() == 1;
        return ((CellCollection) term).cells().entries().iterator().next().getValue();
    }

}
