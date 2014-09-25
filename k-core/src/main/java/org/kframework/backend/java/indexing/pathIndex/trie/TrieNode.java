// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.trie;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * A single node in the trie.
 * <p/>
 * Author: Owolabi Legunsen
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class TrieNode implements Serializable{
    private final String value;
    private ArrayList<TrieNode> children;

    private final Set<Integer> indices;

    public TrieNode(String value) {
        this.value = value;
        indices = new LinkedHashSet<>();
    }

    /**
     * Checks whether any of the children of this node holds a particular value.
     *
     * @param value The value that we are looking for
     * @return true if the children of this node contain the value passed in. false otherwise
     */
    public boolean inChildren(String value) {
        boolean contained = false;
        for (TrieNode node : getChildren()) {
            if (node.getValue().equals(value)) {
                contained = true;
                break;
            }
        }
        return contained;
    }

    /**
     * Fetches the child of this node which has a particular value.
     *
     * @param value The value that we are looking for.
     * @return The child of this node which has the value that we are looking for, if there is one,
     *         or null if there is none.
     */
    public TrieNode getChild(String value) {
        TrieNode child = null;
        for (TrieNode node : getChildren()) {
            if (node.getValue().equals(value)) {
                child = node;
            }
        }
        return child;
    }

    public String getValue() {
        return value;
    }

    public ArrayList<TrieNode> getChildren() {
        return children;
    }

    public void setChildren(ArrayList<TrieNode> children) {
        this.children = children;
    }

    public Set<Integer> getIndices() {
        return indices;
    }

    @Override
    public String toString() {
        return value;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TrieNode trieNode = (TrieNode) o;

        if (children != null ? !children.equals(trieNode.children) : trieNode.children != null)
            return false;
        return value.equals(trieNode.value);
    }

    @Override
    public int hashCode() {
        int result = value.hashCode();
        result = 31 * result + (children != null ? children.hashCode() : 0);
        return result;
    }
}
