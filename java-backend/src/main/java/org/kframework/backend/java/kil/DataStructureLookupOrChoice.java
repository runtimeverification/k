// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

public interface DataStructureLookupOrChoice {
    Term base();

    class Util {
        public static KItem of(Term base, Term key, TermContext context) {
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

        public static DataStructureChoice of(DataStructureChoice.Type type, Term base) {
            switch (type) {
            case MAP_KEY_CHOICE:
                return new MapKeyChoice(base);
            case SET_ELEMENT_CHOICE:
                return new SetElementChoice(base);
            default:
                assert false : "unimplemented missing case";
                return null;
            }
        }
    }

}
