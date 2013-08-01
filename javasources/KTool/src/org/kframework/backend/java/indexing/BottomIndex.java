package org.kframework.backend.java.indexing;


/**
 * @author: AndreiS
 */
public class BottomIndex implements Index {

    public static final BottomIndex BOTTOM = new BottomIndex();

    private BottomIndex() { }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof BottomIndex || index instanceof TopIndex;
    }

    @Override
    public String toString() {
        return "@Bottom";
    }

}
