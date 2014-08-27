// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.EnumHashBiMap;


/**
 * Enumeration of the kinds of K. Seven different kinds are currently available
 * in the Java backend: <li>{@code Kind#BOTTOM} <li>{@code Kind#CELL} <li>
 * {@code Kind#CELL_COLLECTION} <li>{@code Kind#K} <li>{@code Kind#KITEM} <li>
 * {@code Kind#KLABEL} <li>{@code Kind#KLIST}
 * <p>
 * <br>
 * Essentially, kinds can be seen as a more coarse-grained categorization of the
 * {@link Term}s than sorts. To be more specific, 1) each sort has a most
 * precise corresponding kind, and 2) two sorts with disjoint kinds are disjoint
 * as well.
 *
 * @author AndreiS
 */
public enum Kind {
    BOTTOM,
    CELL,
    CELL_COLLECTION,
    K,
    KITEM,
    KLABEL,
    KLIST;
    //MAP;

    /**
     * Stores sorts of all the available {@code Kind}s.
     */
    private static final EnumHashBiMap<Kind, Sort> sorts = EnumHashBiMap.create(Kind.class);

    static {
        sorts.put(BOTTOM, Sort.BOTTOM);
        sorts.put(CELL, Sort.BAG_ITEM);
        sorts.put(CELL_COLLECTION, Sort.BAG);
        sorts.put(K, Sort.KSEQUENCE);
        sorts.put(KITEM, Sort.KITEM);
        sorts.put(KLABEL, Sort.KLABEL);
        sorts.put(KLIST, Sort.KLIST);
    }

    /**
     * @param sort
     *            the sort
     * @return the kind of the given sort
     */
    public static Kind of(Sort sort) {
        Kind kind = sorts.inverse().get(sort);
        if (kind != null) {
            return kind;
        } else {
            return KITEM;
        }
    }

    /**
     * Returns {@code true} if {@code this} kind is one of
     * {@link org.kframework.backend.java.kil.Kind.KItem},
     * {@link org.kframework.backend.java.kil.Kind.K}, or
     * {@link org.kframework.backend.java.kil.Kind.KList}.
     */
    public boolean isComputational() {
        return this == Kind.KITEM || this == Kind.K || this == Kind.KLIST;
    }

    /**
     * Returns {@code true} if {@code this} kind is one of
     * {@link org.kframework.backend.java.kil.Kind.CELL} or
     * {@link org.kframework.backend.java.kil.Kind.CELL_COLLECTION}.
     */
    public boolean isStructural() {
        return this == Kind.CELL || this == Kind.CELL_COLLECTION;
    }

    public Sort asSort() {
        return sorts.get(this);
    }

    @Override
    public String toString() {
        return sorts.get(this).name();
    }

}
