package org.kframework.backend.java.indexing.pathIndex.trie;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * A leaf node in the trie, i.e., one that has no children
 * <p/>
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
}
