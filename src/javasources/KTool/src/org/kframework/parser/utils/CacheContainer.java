// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import org.kframework.kil.Sentence;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by Radu on 05.06.2014.
 *
 * Stores the contents of each parsed rule.
 */
public class CacheContainer implements Serializable {
    /**
     * Total number of sentences that have been tried to be parsed.
     */
    public int totalSentences = 0;
    /**
     * The sentences that have been found in the cache.
     */
    public int parsedSentences = 0;
    /**
     * Mapping from moduleName + the string representation of the rule to the AST representation
     */
    public Map<String, CachedSentence> sentences = new HashMap<>();

    /**
     * Wrapper around the Sentence used just for caching purposes.
     * I need to store the location information so I can update the future locations.
     */
    public class CachedSentence implements Serializable {
        public final Sentence sentence;
        public final int startLine;
        public final int startColumn;

        public CachedSentence(Sentence sentence, int startLine, int startColumn) {
            this.sentence = sentence;
            this.startLine = startLine;
            this.startColumn = startColumn;
        }
    }
}
