package org.kframework.backend.java.indexing.pathIndex.trie;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Author: Owolabi Legunsen
 * 1/2/14: 7:30 PM
 */
public class TrieLeaf extends TrieNode {
    public Set<Integer> getIndices() {
        return indices;
    }

    private final Set<Integer> indices;

    public TrieLeaf(String value, int index) {
        super(value);

        indices = new LinkedHashSet<>();
        indices.add(index);
    }


    @Override
    public String toString() {
        return getValue() + " => " + getIndices();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        TrieLeaf trieLeaf = (TrieLeaf) o;

        return indices.equals(trieLeaf.indices);

    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + indices.hashCode();
        return result;
    }
}
