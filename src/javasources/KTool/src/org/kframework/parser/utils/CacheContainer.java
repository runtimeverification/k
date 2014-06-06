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
    public Map<String, Sentence> sentences = new HashMap<>();
}
