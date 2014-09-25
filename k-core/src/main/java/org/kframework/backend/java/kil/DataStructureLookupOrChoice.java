// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

public interface DataStructureLookupOrChoice {
    Term base();

    class Util {
        public static DataStructureLookup of(DataStructureLookup.Type type, Term base, Term key, Kind kind) {
            switch (type) {
            case MAP_LOOKUP:
                return new MapLookup(base, key, kind);
            case LIST_LOOKUP:
                return new ListLookup(base, key, kind);
            case SET_LOOKUP:
                return new SetLookup(base, key);
            default:
                assert false : "unimplemented missing case";
                return null;
            }
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
