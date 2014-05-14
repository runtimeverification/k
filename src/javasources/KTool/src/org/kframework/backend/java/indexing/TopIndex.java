// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;


import java.util.HashMap;

/**
 * @author: AndreiS
 */
public class TopIndex implements Index {

    public static final TopIndex TOP = new TopIndex();

    private TopIndex() { }

    private Object readResolve() {
        return TOP;
    }

    @Override
    public boolean isUnifiable(Index index) {
        return true;
    }

    @Override
    public int hashCode() {
        return 1;
    }

    @Override
    public String toString() {
        return "@Top";
    }
}
