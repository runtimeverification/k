package org.kframework.utils;

import java.util.NoSuchElementException;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;


public interface BitSet<T extends BitSet<?>> extends Cloneable {

    static BitSet apply(int length) {
        if (length <= Long.SIZE) {
            return new OneWordBitSet();
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
                    next = nextSetBit(next+1);
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

    void or(T that);
    void and(T that);
    boolean intersects(T other);

    boolean get(int i);
    void set(int i);
    int nextSetBit(int i);

    boolean isEmpty();
    int length();
    int cardinality();

    void makeOnes(int length);

    T clone();

}
