package org.kframework.backend.java.indexing;


/**
 * @author: AndreiS
 */
public class BottomIndex implements Index {

    private final String Id = "@Bottom";
    public static final BottomIndex BOTTOM = new BottomIndex();

    private BottomIndex() { }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof BottomIndex || index instanceof TopIndex;
    }
    
    @Override
    public String toString() {
        return Id;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BottomIndex that = (BottomIndex) o;

        if (!Id.equals(that.Id)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return Id.hashCode();
    }
}
