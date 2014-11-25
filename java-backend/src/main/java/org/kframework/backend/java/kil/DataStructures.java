// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

public interface DataStructures {

    static KItem lookup(Term base, Term key, TermContext context) {
        KLabelConstant klabel;
        if (base.sort().equals(Sort.LIST)) {
            klabel = KLabelConstant.of("List:get", context.definition().context());
        } else if (base.sort().equals(Sort.MAP)) {
            klabel = KLabelConstant.of("Map:lookup", context.definition().context());
        } else if (base.sort().equals(Sort.SET)) {
            klabel = KLabelConstant.of("'_in_", context.definition().context());
        } else {
            assert false : "unimplemented missing case";
            return null;
        }
        return KItem.of(klabel, KList.concatenate(base, key), context);
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

    static Term getBase(Term term) {
        assert isLookup(term);
        return ((KList) (((KItem) term).kList())).get(0);

    }

    static Term getKey(Term term) {
        assert isLookup(term);
        return ((KList) (((KItem) term).kList())).get(1);

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

}
