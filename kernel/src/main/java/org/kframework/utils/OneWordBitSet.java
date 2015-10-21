// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.utils;

/**
 * {@link BitSet} implementation backed by a single work.
 */
public class OneWordBitSet implements BitSet<OneWordBitSet> {

    private static final long WORD_MASK = 0xffffffffffffffffL;

    private long word;

    public OneWordBitSet(long word) {
        this.word = word;
    }

    public OneWordBitSet() {
        this(0);
    }

    @Override
    public void or(OneWordBitSet bitSet) {
        word |= bitSet.word;
    }

    @Override
    public void and(OneWordBitSet bitSet) {
        word &= bitSet.word;
    }

    @Override
    public boolean intersects(OneWordBitSet bitSet) {
        return (word & bitSet.word) != 0;
    }

    @Override
    public boolean subset(OneWordBitSet bitSet) {
        return word == (word & bitSet.word);
    }

    @Override
    public boolean get(int i) {
        assert i < size();
        return (word & 1L << i) != 0;
    }

    @Override
    public void set(int i) {
        assert i < size();
        word |= 1L << i;
    }

    @Override
    public void clear(int i) {
        assert i < size();
        word &= ~(1L << i);
    }

    @Override
    public int nextSetBit(int i) {
        assert i <= size();
        long maskedWord = word & (WORD_MASK << i);
        return maskedWord == 0 ? -1 : Long.numberOfTrailingZeros(maskedWord);
    }

    @Override
    public boolean isEmpty() {
        return word == 0;
    }

    @Override
    public int cardinality() {
        return Long.bitCount(word);
    }

    @Override
    public int length() {
        return Long.SIZE - Long.numberOfLeadingZeros(word);
    }

    @Override
    public int size() {
        return Long.SIZE;
    }

    @Override
    public void clear() {
        word = 0;
    }

    @Override
    public OneWordBitSet clone() {
        return new OneWordBitSet(word);
    }

}
