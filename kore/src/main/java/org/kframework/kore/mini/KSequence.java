// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.K;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KSequence implements org.kframework.kore.KSequence {

    private final K[] items;

    public KSequence(K... items) {
        this.items = items;
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public List<K> items() {
        return Arrays.asList(items);
    }

    @Override
    public int size() {
        return items.length;
    }

    @Override
    public Iterable<? extends K> asIterable() {
        return Arrays.asList(items);
    }

    @Override
    public Stream<K> stream() {
        return Arrays.stream(items);
    }

    @Override
    public Att att() {
        return Att.empty();
    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KSequence kSequence = (KSequence) o;

        // Probably incorrect - comparing Object[] arrays with Arrays.equals
        return Arrays.equals(items, kSequence.items);

    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(items);
    }
}
