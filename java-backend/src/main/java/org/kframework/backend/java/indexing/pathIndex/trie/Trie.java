// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.trie;

import java.util.Set;

/**
 * An interface for Trie implementations. PathIndexTrie is the only current implementation but we
 * may need to add more if we explore other indexing techniques.
 *
 * Author: Owolabi Legunsen
 * 1/2/14: 4:34 PM
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public interface Trie {
    public void addIndex(TrieNode trie, String pString, int value);

//    public void removeIndex(TrieNode trieNode, String pString, int value);

    public Set<Integer> retrieve(TrieNode trieNode, String queryString);

    public boolean isMember(TrieNode trieNode, String queryString);

    public TrieNode getRoot();
}
