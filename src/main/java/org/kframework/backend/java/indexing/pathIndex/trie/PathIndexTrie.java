// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.trie;


import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * This class implements a trie, the data structure that supports the operations of the Path
 * Indexing technique.
 * Author: Owolabi Legunsen
 * 1/2/14: 7:52 PM
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class PathIndexTrie implements Trie,Serializable {
    public static final String ROOT_SYMBOL = "@";
    private final TrieNode root;
    private final String delimiter = "\\.";

    public PathIndexTrie() {
        root = new TrieNode(ROOT_SYMBOL);
    }

    /**
     * This method adds a new string to the index
     *
     * @param trieNode node to start adding the string. should always be root
     * @param pString  the string to add
     * @param value    the value associated with this string i.e. given this string,
     *                 we want to get this value back
     */
    @Override
    public void addIndex(TrieNode trieNode, String pString, int value) {
        //we are at the end of the string to be inserted
        //base case
        if (pString.length() == 0) {
            return;
        }
        String[] split = pString.split(delimiter);
        ArrayList<String> splitList = new ArrayList<>(Arrays.asList(split));
        add(trieNode, splitList, value);
    }

    /**
     * Helper method that recursively traverses the current data structure and then adds the new
     * P-String to the right places.
     *
     * @param trieNode  The node to start the insertion from
     * @param strings   A list of strings obtained from splitting up the initial pString
     * @param value     The value to be associated with the inserted string in the trie
     */
    private void add(TrieNode trieNode, ArrayList<String> strings, int value) {
        if (strings.size() == 0) {
            return;
        }

        String elem = strings.get(0);

        ArrayList<String> splitList1 = new ArrayList<>(strings.subList(1, strings.size()));

        if (trieNode.getChildren() == null) {
            //if we are also at the end of the pString
            if (strings.size() == 1) {
                //if the current node is a leaf, add value to its value set and return
                if (trieNode instanceof TrieLeaf) {
                    trieNode.getIndices().add(value);
                    return;
                } else {
                    TrieNode leaf = new TrieLeaf(elem, value);
                    trieNode.setChildren(new ArrayList<TrieNode>());
                    trieNode.getChildren().add(leaf);
                    trieNode.getIndices().add(value);
                    return;
                }
            }

            //otherwise just continue adding
            TrieNode newNode = new TrieNode(elem);
            trieNode.setChildren(new ArrayList<TrieNode>());
            trieNode.getChildren().add(newNode);
            trieNode.getIndices().add(value);
            add(newNode, splitList1, value);
        }

        // we are at the end of the string to be added, but the current node has
        // a child that has the same string value as the last element of the
        // input list. make that child a leaf if it is not already one and store
        // the value in there
        if (strings.size() == 1 && trieNode.getChildren() != null) {
            if (trieNode.inChildren(elem)) {
                TrieNode node = trieNode.getChild(elem);
                if (node instanceof TrieLeaf && elem.equals(node.getValue())) {
                    node.getIndices().add(value);
                    trieNode.getIndices().add(value);
                    return;
                }

                if (node instanceof TrieLeaf && !elem.equals(node.getValue())) {
                    //TODO(Owolabi): remove this
                    throw new IllegalArgumentException();
                }

                if (!(node instanceof TrieLeaf)) {
                    TrieNode newNode = new TrieLeaf(elem, value);
                    newNode.setChildren(node.getChildren());
                    trieNode.getChildren().remove(node);
                    trieNode.getIndices().add(value);
                    trieNode.getChildren().add(newNode);
                    return;
                }
            }
        }

        //one of the children of the current node already contains the next string
        // to be added. continue adding from that child node.
        if (trieNode.getChildren() != null && trieNode.inChildren(elem)) {
            trieNode.getIndices().add(value);
            TrieNode node = trieNode.getChild(elem);
            add(node, splitList1, value);
        }

        //none of the children of the current node already contains the next string
        // to be added. Add a new child to the current node and continue adding
        // from there
        if (trieNode.getChildren() != null && !trieNode.inChildren(elem)) {
            if (strings.size() == 1) {
                trieNode.getIndices().add(value);
                TrieNode leaf = new TrieLeaf(elem, value);
                trieNode.getChildren().add(leaf);
                return;
            }
            trieNode.getIndices().add(value);
            TrieNode newNode = new TrieNode(elem);
            trieNode.getChildren().add(newNode);
            add(newNode, splitList1, value);
        }
    }

    /**
     * Retrieve the index set associated with a given query (p)String
     *
     * @param trieNode    the node to start checking from
     * @param queryString the pString that we are looking for
     * @return the set of indices associated with the query pString, or null if it is not found
     */
    @Override
    public Set<Integer> retrieve(TrieNode trieNode, String queryString) {
        String[] split = queryString.split(delimiter);
        ArrayList<String> splitList = new ArrayList<>(Arrays.asList(split));
        ArrayList<String> subList = new ArrayList<>(splitList.subList(1, splitList.size()));
        return retrieveSet(trieNode, subList);
    }

    private Set<Integer> retrieveSet(TrieNode trieNode, ArrayList<String> splitList) {
        if (splitList.size() == 0) {
            return new LinkedHashSet<>();
        }
        String firstString = splitList.get(0);
        ArrayList<String> subList = new ArrayList<>(splitList.subList(1, splitList.size()));
        TrieNode child = trieNode.getChild(firstString);
        if (child != null) {
            if (trieNode.getValue().equals(ROOT_SYMBOL)) {
                if (splitList.size() == 1 && (child instanceof TrieLeaf)) {
                    return child.getIndices();
                }
                return retrieveSet(child, subList);
            }
        } else {
            if (!trieNode.getValue().equals(ROOT_SYMBOL)) {
                return trieNode.getIndices();
            }
        }

        if (splitList.size() == 1) {
            if (child != null) {
                return child.getIndices();
            } else {
                if (!trieNode.getValue().equals(ROOT_SYMBOL)) {
                    return trieNode.getIndices();
                }
            }

        } else if (splitList.size() > 1 && child != null) {
            return retrieveSet(child, subList);
        }

        return null;
    }

    /**
     * Checks membership of a key in the index
     *
     * @param trieNode    the node to start searching from
     * @param queryString the string to find
     * @return True if and only if queryString is an key in the index trie
     *         which starts from trieNode. In order words, if rob => X is in
     *         the trie, but ro => ? is not, then it will return false.
     */
    @Override
    public boolean isMember(TrieNode trieNode, String queryString) {
        boolean isMember = false;

        if (trieNode == null || queryString.length() == 0) {
            return false;
        }

        return isMember;
    }

    //TODO(OwolabiL): print in a better way, like in weka's Trie.java
    @Override
    public String toString() {
        return print(root);
    }

    private String print(TrieNode root) {
        StringBuilder tree = new StringBuilder(root.toString());

        if (root.getChildren() == null) {
            return tree.append("").toString();
        } else {
            for (TrieNode node : root.getChildren()) {
                tree.append(print(node));
            }
        }

        return tree.toString();
    }

    @Override
    public TrieNode getRoot() {
        return root;
    }
}
