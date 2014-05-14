// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;


/**
 * @author: AndreiS
 */
public class BottomIndex implements Index {

    public static final BottomIndex BOTTOM = new BottomIndex();

    private BottomIndex() { }

    private Object readResolve() {
        return BOTTOM;
    }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof BottomIndex || index instanceof TopIndex;
    }

    @Override
    public int hashCode() {
        return 0;
    }

    @Override
    public String toString() {
        return "@Bottom";
    }
}
