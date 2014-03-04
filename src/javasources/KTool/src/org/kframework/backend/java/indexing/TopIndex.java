package org.kframework.backend.java.indexing;


/**
 * @author: AndreiS
 */
public class TopIndex implements Index {

    private final String Id = "@Top";
    public static final TopIndex TOP = new TopIndex();

    private TopIndex() { }

    @Override
    public boolean isUnifiable(Index index) {
        return true;
    }
    
    @Override
    public String toString() {
        return Id;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TopIndex topIndex = (TopIndex) o;

        if (!Id.equals(topIndex.Id)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return Id.hashCode();
    }
}
