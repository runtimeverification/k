// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.trie;

import java.io.Serializable;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * A leaf node in the trie, i.e., one that has no children
 * <p/>
 * Author: Owolabi Legunsen
 *
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class TrieLeaf extends TrieNode implements Serializable{
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
