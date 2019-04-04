// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.builtin.Sorts;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.io.ObjectStreamException;
import java.io.Serializable;
import org.kframework.kore.KORE;
import scala.collection.Seq;

import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Sort of a {@link Term}.
 *
 * @author YilongL
 *
 */
public final class Sort implements org.kframework.kore.Sort, Serializable {

    private static final ConcurrentMap<String, Sort> cache = new ConcurrentHashMap<>();

    /**
     * see {@link #ordinal()}
     */
    public static final AtomicInteger maxOrdinal = new AtomicInteger(0);


    public static final Sort KITEM          =   Sort.of(Sorts.KItem());
    public static final Sort KSEQUENCE      =   Sort.of(Sorts.K());
    public static final Sort KLIST          =   Sort.of(Sorts.KList());
    public static final Sort KLABEL         =   Sort.of(Sorts.KLabel());
    public static final Sort KRESULT        =   Sort.of(Sorts.KResult());

    public static final Sort BAG            =   Sort.of(Sorts.Bag());
    public static final Sort LIST           =   Sort.of(Sorts.List());
    public static final Sort MAP            =   Sort.of(Sorts.Map());
    public static final Sort SET            =   Sort.of(Sorts.Set());

    public static final Sort INT            =   Sort.of(Sorts.Int());
    public static final Sort BOOL           =   Sort.of(Sorts.Bool());
    public static final Sort FLOAT          =   Sort.of(Sorts.Float());
    public static final Sort STRING         =   Sort.of(Sorts.String());
    public static final Sort BIT_VECTOR     =   Sort.of(Sorts.MInt());

    public static final Sort KVARIABLE      =   Sort.of(KORE.Sort("KVar"));

    public static final Sort META_VARIABLE  =   Sort.of(KORE.Sort("MetaVariable"));
    public static final Sort BOTTOM         =   Sort.of(KORE.Sort("#Bottom"));

    /**
     * {@code String} representation of this {@code Sort}.
     */
    private final String name;
    private final Seq<org.kframework.kore.Sort> params;

    private final int ordinal;

    /**
     * Gets the corresponding {@code Sort} from its {@code String}
     * representation.
     *
     * @param name
     *            the name of the sort
     * @return the sort
     */
    public static Sort of(org.kframework.kore.Sort sort) {
        return cache.computeIfAbsent(sort.toString(), s -> new Sort(sort.name(), sort.params(), maxOrdinal.getAndIncrement()));
    }


    private Sort(String name, Seq<org.kframework.kore.Sort> params, int ordinal) {
        this.name = name;
        this.params = params;
        this.ordinal = ordinal;
    }

    public String name() {
        return name;
    }

    @Override
    public Seq<org.kframework.kore.Sort> params() {
        return params;
    }

    public int ordinal() {
        return ordinal;
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    public String toString() {
        return name;
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if
     * there is a cached instance.
     */
    Object readResolve() throws ObjectStreamException {
        if (cache.containsKey(name) && cache.get(name).ordinal != this.ordinal) {
            throw KEMException.criticalError("The ordinal for sort: " + name + " is " + cache.get(name).ordinal +
                    " in the cache and " + this.ordinal + " serialized.");
        }
        // TODO: fix bug: ordinals from deserialized objects may overlap with those of newly created objects
        return cache.computeIfAbsent(name, x -> this);
    }

    public static Sort parse(String s) {
        return of(Outer.parseSort(s));
    }
}
