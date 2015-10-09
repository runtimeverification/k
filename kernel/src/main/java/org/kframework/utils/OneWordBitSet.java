package org.kframework.utils;


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
    public boolean get(int i) {
        assert i < Long.SIZE;
        return (word & ((long) 1) << i) != 0;
    }

    @Override
    public void set(int i) {
        assert i < Long.SIZE;
        word |= ((long) 1) << i;
    }

    @Override
    public int nextSetBit(int i) {
        assert i <= Long.SIZE;
        long maskedWord = word & (WORD_MASK << i);
        return maskedWord == 0 ? -1 : Long.numberOfTrailingZeros(maskedWord);
    }

    @Override
    public boolean isEmpty() {
        return word == 0;
    }

    @Override
    public int length() {
        return Long.SIZE - Long.numberOfLeadingZeros(word);
    }

    @Override
    public int cardinality() {
        return Long.bitCount(word);
    }

    @Override
    public void makeOnes(int length) {
        assert length < Long.SIZE;
        word = (((long) 1) << length) - 1;
    }

    @Override
    public OneWordBitSet clone() {
        return new OneWordBitSet(word);
    }

}
