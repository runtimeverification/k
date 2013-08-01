package org.kframework.backend.java.indexing;


/**
 * @author: AndreiS
 */
public class TopIndex implements Index {

    public static final TopIndex TOP = new TopIndex();

    private TopIndex() { }

    @Override
    public boolean isUnifiable(Index index) {
        return true;
    }

    @Override
    public String toString() {
        return "@Top";
    }

}
