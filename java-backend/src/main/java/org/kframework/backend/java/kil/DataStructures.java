// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;

import java.util.Map;
import java.util.Set;


/**
 * Contains helper methods for handling data structures and operations (lookup, update, ...) on data structures.
 *
 * @author AndreiS
 */
public interface DataStructures {

    static KItem lookup(Term base, Term key, TermContext context) {
        KLabelConstant klabel;
        KList kList;
        if (base.sort().equals(Sort.LIST)) {
            klabel = KLabelConstant.of("List:get", context.definition().context());
            kList = (KList) KList.concatenate(base, key);
        } else if (base.sort().equals(Sort.MAP)) {
            klabel = KLabelConstant.of("Map:lookup", context.definition().context());
            kList = (KList) KList.concatenate(base, key);
        } else if (base.sort().equals(Sort.SET)) {
            klabel = KLabelConstant.of("'_in_", context.definition().context());
            kList = (KList) KList.concatenate(key, base);
        } else {
            assert false : "unimplemented missing case";
            return null;
        }
        return KItem.of(klabel, kList, context);
    }

    static boolean isLookup(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && (((KItem) term).kLabel().toString().equals("List:get")
                        || ((KItem) term).kLabel().toString().equals("Map:lookup")
                        || ((KItem) term).kLabel().toString().equals("'_in_"))
                && ((KItem) term).kList() instanceof KList
                && ((KList) ((KItem) term).kList()).isConcreteCollection()
                && ((KList) ((KItem) term).kList()).concreteSize() == 2;
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
            klabel = KLabelConstant.of("Map:choice", context.definition().context());
        } else if (base.sort().equals(Sort.SET)) {
            klabel = KLabelConstant.of("Set:choice", context.definition().context());
        } else {
            assert false : "unimplemented missing case";
            return null;
        }
        return KItem.of(klabel, KList.singleton(base), context);
    }

    static Term listRange(Term base, int removeLeft, int removeRight, TermContext context) {
        if (removeLeft == 0 && removeRight == 0) {
            return base;
        }

        return KItem.of(
                KLabelConstant.of("List:range", context.definition().context()),
                KList.concatenate(base, IntToken.of(removeLeft), IntToken.of(removeRight)),
                context);
    }

    static Term mapRemoveAll(Term base, Set<Term> removeSet, TermContext context) {
        if (removeSet.isEmpty()) {
            return base;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(removeSet);
        return KItem.of(
                KLabelConstant.of("'removeAll", context.definition().context()),
                KList.concatenate(base, builder.build()),
                context);
    }

    static Term mapUpdateAll(Term base, Map<Term, Term> updateMap, TermContext context) {
        if (updateMap.isEmpty()) {
            return base;
        }

        BuiltinMap.Builder builder = new BuiltinMap.Builder();
        builder.putAll(updateMap);
        return KItem.of(
                KLabelConstant.of("'updateMap", context.definition().context()),
                KList.concatenate(base, builder.build()),
                context);
    }

    static Term setDifference(Term base, Set<Term> removeSet, TermContext context) {
        if (removeSet.isEmpty()) {
            return base;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder();
        builder.addAll(removeSet);
        return KItem.of(
                KLabelConstant.of("'_-Set_", context.definition().context()),
                KList.concatenate(base, builder.build()),
                context);
    }

    static boolean isMapUpdate(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && ((KItem) term).kLabel().toString().equals("'updateMap")
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

}
