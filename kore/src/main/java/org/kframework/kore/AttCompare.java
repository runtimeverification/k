package org.kframework.kore;

/**
 * Created by dwightguth on 6/17/15.
 */
public class AttCompare {
    private K k;
    private String[] attNames;

    public AttCompare(K k, String... attNames) {
        this.k = k;
        this.attNames = attNames;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        AttCompare that = (AttCompare) o;

        return k.attEquals(that.k, attNames);

    }

    @Override
    public String toString() {
        return k.toString();
    }

    @Override
    public int hashCode() {
        return k.hashCode();
    }

    public K get() {
        return k;
    }
}
