package org.kframework.backend.java.indexing.pathIndex.trie;

import java.util.*;

/**
 * Author: Owolabi Legunsen
 * 1/2/14: 7:52 PM
 */
public class PathIndexTrie implements Trie {
    private final TrieNode root;
    private final String delimiter = "\\.";

    public PathIndexTrie() {
        root = new TrieNode("@");
    }

    /**
     * This method adds a new string to the index
     * TODO: convert this to a graph labelled by the chars in the string (like in "Term Indexing" book
     * TODO: How much faster is this stuff?
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
     * Inspired by implementation of Trie#remove in weka
     * <p/>
     * TODO(OwolabiL): Needs to be fixed for cases when there is more than one value at the leaf
     *
     * @param node    to start removal from
     * @param pString pString to remove
     */
    @Override
    public void removeIndex(TrieNode node, String pString, int value) {
        String[] split = pString.split(delimiter);
        ArrayList<String> splitList = new ArrayList<>(Arrays.asList(split));
        remove(node, splitList, value);
    }

    private void remove(TrieNode node, ArrayList<String> splitList, int value) {
        String c;
        ArrayList<String> newSuffix;
        TrieNode child = null;

        c = splitList.get(0);
        if (splitList.size() == 1) {
            newSuffix = new ArrayList<>();
        } else {
            newSuffix = new ArrayList<>(splitList.subList(1, splitList.size()));
        }

        //TODO(OwolabiL): replace with node.getChild
        ArrayList<TrieNode> children = node.getChildren();
        for (TrieNode cnode : children) {
            if (cnode.getValue().equals(c)) {
                child = cnode;
                break;
            }
        }

//        if (child == null) {
////            result = false;
//        } else

        if (newSuffix.size() == 0) {
            if (child instanceof TrieLeaf && child.getIndices().size() > 0) {
                children.remove(child);
            }
        } else {
            remove(child, newSuffix, value);

            if (child != null) {
                if (child.getChildren().size() == 0) {
                    children.remove(child);
                }
            }
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
            return new HashSet<>();
        }
        String firstString = splitList.get(0);
        ArrayList<String> subList = new ArrayList<>(splitList.subList(1, splitList.size()));
        TrieNode child = trieNode.getChild(firstString);
        if (child != null) {
            if (trieNode.getValue().equals("@")) {
                if (splitList.size() == 1 && (child instanceof TrieLeaf)) {
                    return child.getIndices();
                }
                return retrieveSet(child, subList);
            }
        }
//        else {
//            return trieNode.getIndices();
//        }

        if (splitList.size() == 1) {
            if (child != null) {
                return child.getIndices();
            } else{
                if (!trieNode.getValue().equals("@")){
                    return trieNode.getIndices();
                }
            }

        } else if (splitList.size() > 1) {
            return retrieveSet(child, subList);
        }

        return null;
    }

    /**
     * Check membership of a key in the index
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

//    int size(TrieNode node) {
//        if (node == null) {
//            //TODO(OwolabiL): Throw an exception instead
//            return -1000;
//        }
//        int size = 1;
//        if (node.getChildren() != null) {
//            for (TrieNode trieNode : node.getChildren()) {
//                size += size(trieNode);
//            }
//        }
//
//        return size;
//    }

    @Override
    public TrieNode getRoot() {
        return root;
    }
}
