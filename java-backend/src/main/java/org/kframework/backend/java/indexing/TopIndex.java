// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

/**
 * @author: AndreiS
 */
public class TopIndex implements Index {

    TopIndex() { }

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
