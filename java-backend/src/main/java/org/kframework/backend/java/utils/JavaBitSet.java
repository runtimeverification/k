// Copyright (c) 2015-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.utils;

/**
 * {@link BitSet} A wrapper class for java's built-in BitSet that is compatible with K's BitSet interface
 */
public class JavaBitSet implements BitSet<JavaBitSet>  {

    private java.util.BitSet bitset = new java.util.BitSet();

    public JavaBitSet(java.util.BitSet bitset){
        this.bitset = bitset;
    }

    public JavaBitSet(){

    }

    @Override
    public void or(JavaBitSet bitSet) {
        this.bitset.or(bitSet.bitset);
    }

    @Override
    public void and(JavaBitSet bitSet) {
        this.bitset.and(bitSet.bitset);
    }

    @Override
    public boolean intersects(JavaBitSet bitSet) {
        return this.bitset.intersects(bitSet.bitset);
    }

    @Override
    public boolean subset(JavaBitSet bitSet) {
        JavaBitSet temp = this.clone();
        temp.and(bitSet);
        return this.bitset.equals(temp.bitset);
    }

    @Override
    public boolean get(int i) {
       return this.bitset.get(i);
    }

    @Override
    public void set(int i) {
        this.bitset.set(i);
    }

    @Override
    public void clear(int i) {
        this.bitset.clear(i);
    }

    @Override
    public int nextSetBit(int i) {
        return this.bitset.nextSetBit(i);
    }

    @Override
    public boolean isEmpty() {
       return this.bitset.isEmpty();
    }

    @Override
    public int length() {
        return this.bitset.length();
    }

    @Override
    public int size() {
        return this.bitset.size();
    }

    @Override
    public int cardinality() {
        return  this.bitset.cardinality();
    }

    @Override
    public void clear() {
        this.bitset.clear();
    }

    @Override
    public JavaBitSet clone() {
        return new JavaBitSet((java.util.BitSet)this.bitset.clone());
    }

    @Override
    public String toString() {
        return this.bitset.toString();
    }

}

