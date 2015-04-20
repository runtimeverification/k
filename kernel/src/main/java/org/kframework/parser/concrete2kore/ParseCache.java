// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.kore.K;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

/**
 * Created by dwightguth on 4/20/15.
 */
public class ParseCache implements Serializable {
    private final ParseInModule parser;
    private final Map<String, ParsedSentence> cache;

    public ParseCache(ParseInModule parser, Map<String, ParsedSentence> cache) {
        this.parser = parser;
        this.cache = cache;
    }

    public Map<String, ParsedSentence> getCache() {
        return cache;
    }

    public ParseInModule getParser() {
        return parser;
    }

    public static class ParsedSentence implements Serializable {
        private final K parse;
        private final Set<ParseFailedException> warnings;

        public ParsedSentence(K parse, Set<ParseFailedException> warnings) {
            this.parse = parse;
            this.warnings = warnings;
        }

        public K getParse() {
            return parse;
        }

        public Set<ParseFailedException> getWarnings() {
            return warnings;
        }
    }
}
