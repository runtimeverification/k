// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.utils;

/**
 * {@link BitSet} implementation backed by four words. Faster than using the JDK {@link java.util.BitSet}.
 */
public class FourWordBitSet implements BitSet<FourWordBitSet> {

    private static final long WORD_MASK = 0xffffffffffffffffL;

    private long word0;
    private long word1;
    private long word2;
    private long word3;

    public FourWordBitSet(long word0, long word1, long word2, long word3) {
        this.word0 = word0;
        this.word1 = word1;
        this.word2 = word2;
        this.word3 = word3;
    }

    public FourWordBitSet() {
        this(0, 0, 0, 0);
    }

    @Override
    public void or(FourWordBitSet bitSet) {
        word0 |= bitSet.word0;
        word1 |= bitSet.word1;
        word2 |= bitSet.word2;
        word3 |= bitSet.word3;
    }

    @Override
    public void and(FourWordBitSet bitSet) {
        word0 &= bitSet.word0;
        word1 &= bitSet.word1;
        word2 &= bitSet.word2;
        word3 &= bitSet.word3;
    }

    @Override
    public boolean intersects(FourWordBitSet bitSet) {
        return (word0 & bitSet.word0) != 0
                || (word1 & bitSet.word1) != 0
                || (word2 & bitSet.word2) != 0
                || (word3 & bitSet.word3) != 0;
    }

    @Override
    public boolean subset(FourWordBitSet bitSet) {
        return word0 == (word0 & bitSet.word0)
                && word1 == (word1 & bitSet.word1)
                && word2 == (word2 & bitSet.word2)
                && word3 == (word3 & bitSet.word3);
    }

    @Override
    public boolean get(int i) {
        assert i < size();

        if (i < Long.SIZE) {
            return (word0 & 1L << i) != 0;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            return (word1 & 1L << i) != 0;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            return (word2 & 1L << i) != 0;
        }
        i -= Long.SIZE;

        return (word3 & 1L << i) != 0;
    }

    @Override
    public void set(int i) {
        assert i < size();

        if (i < Long.SIZE) {
            word0 |= 1L << i;
            return;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            word1 |= 1L << i;
            return;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            word2 |= 1L << i;
            return;
        }
        i -= Long.SIZE;

        word3 |= 1L << i;
    }

    @Override
    public void clear(int i) {
        assert i < size();

        if (i < Long.SIZE) {
            word0 &= ~(1L << i);
            return;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            word1 &= ~(1L << i);
            return;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            word2 &= ~(1L << i);
            return;
        }
        i -= Long.SIZE;

        word3 &= ~(1L << i);
    }

    @Override
    public int nextSetBit(int i) {
        assert i <= size();

        if (i < Long.SIZE) {
            long maskedWord = word0 & (WORD_MASK << i);
            if (maskedWord != 0) {
                return Long.numberOfTrailingZeros(maskedWord);
            }
            i = Long.SIZE;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            long maskedWord = word1 & (WORD_MASK << i);
            if (maskedWord != 0) {
                return Long.numberOfTrailingZeros(maskedWord) + Long.SIZE;
            }
            i = Long.SIZE;
        }
        i -= Long.SIZE;

        if (i < Long.SIZE) {
            long maskedWord = word2 & (WORD_MASK << i);
            if (maskedWord != 0) {
                return Long.numberOfTrailingZeros(maskedWord) + 2 * Long.SIZE;
            }
            i = Long.SIZE;
        }
        i -= Long.SIZE;

        long maskedWord = word3 & (WORD_MASK << i);
        return maskedWord == 0 ? -1 : Long.numberOfTrailingZeros(maskedWord) + 3 * Long.SIZE;
    }

    @Override
    public boolean isEmpty() {
        return word0 == 0
                && word1 == 0
                && word2 == 0
                && word3 == 0;
    }

    @Override
    public int length() {
        //return Long.SIZE - Long.numberOfLeadingZeros(word);
        return size();
    }

    @Override
    public int size() {
        return 4 * Long.SIZE;
    }

    @Override
    public int cardinality() {
        return Long.bitCount(word0) + Long.bitCount(word1) + Long.bitCount(word2) + Long.bitCount(word3);
    }

    @Override
    public void clear() {
        word0 = 0;
        word1 = 0;
        word2 = 0;
        word3 = 0;
    }

    @Override
    public FourWordBitSet clone() {
        return new FourWordBitSet(word0, word1, word2, word3);
    }

}
