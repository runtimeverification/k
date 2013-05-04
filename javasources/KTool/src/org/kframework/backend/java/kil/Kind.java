package org.kframework.backend.java.kil;

import com.google.common.collect.EnumHashBiMap;


/**
 * Enumeration of the kinds of K
 */
public enum Kind {
    BUILTIN,
    CELL,
    CELL_COLLECTION,
    K,
    KITEM,
    KLABEL,
    KLIST,
    MAP;

    private static final EnumHashBiMap<Kind, String> names
            = EnumHashBiMap.create(Kind.class);
    static {
        names.put(BUILTIN, "Builtin");
        names.put(CELL, "Cell");
        names.put(CELL_COLLECTION, "Bag");
        names.put(K, "K");
        names.put(KITEM, "KItem");
        names.put(KLABEL, "KLabel");
        names.put(KLIST, "KList");
        names.put(MAP, "Map");
    }

    /**
     * Returns the {@link Kind} of the given sort
     *
     * @param sort
     * @return
     */
    public static Kind of(String sort) {
        Kind kind = names.inverse().get(sort);
        if (kind != null) {
            return kind;
        } else {
            return KITEM;
        }
    }

    @Override
    public String toString() {
        return names.get(this);
    }
}
