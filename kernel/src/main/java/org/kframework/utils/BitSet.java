// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.utils;

import java.util.NoSuchElementException;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;

/**
 * Generic interface for BitSets so we can easily switch implementations.
 */
public interface BitSet<T extends BitSet<?>> extends Cloneable {

    static BitSet apply(int length) {
        if (length <= Long.SIZE) {
            return new OneWordBitSet();
        } else if (length <= 4 * Long.SIZE) {
            return new FourWordBitSet();
        } else {
            return new OneIntegerGenericBitSet();
        }
    }

    default IntStream stream() {
        class BitSetIterator implements PrimitiveIterator.OfInt {
            int next = nextSetBit(0);

            @Override
            public boolean hasNext() {
                return next != -1;
            }

            @Override
            public int nextInt() {
                if (next != -1) {
                    int ret = next;
                    next = nextSetBit(next + 1);
                    return ret;
                } else {
                    throw new NoSuchElementException();
                }
            }
        }

        return StreamSupport.intStream(
                () -> Spliterators.spliterator(
                        new BitSetIterator(), cardinality(),
                        Spliterator.ORDERED | Spliterator.DISTINCT | Spliterator.SORTED),
                Spliterator.SIZED | Spliterator.SUBSIZED |
                        Spliterator.ORDERED | Spliterator.DISTINCT | Spliterator.SORTED,
                false);
    }

    default void makeOnes(int size) {
        for (int i = 0; i < size; i++) {
            set(i);
        }
    }

    void or(T bitSet);
    void and(T bitSet);
    boolean intersects(T bitSet);
    boolean subset(T bitSet);

    boolean get(int i);
    void set(int i);
    void clear(int i);
    int nextSetBit(int i);

    boolean isEmpty();
    int cardinality();
    int length();
    int size();

    void clear();

    T clone();

}
