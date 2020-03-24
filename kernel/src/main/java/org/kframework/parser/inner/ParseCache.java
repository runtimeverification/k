// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.utils.errorsystem.KEMException;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

/**
 * Created by dwightguth on 4/20/15.
 */
public class ParseCache implements Serializable {
    private final Module module;
    private final boolean strict;
    private final Map<String, ParsedSentence> cache;

    public ParseCache(Module module, boolean strict, Map<String, ParsedSentence> cache) {
        this.module = module;
        this.strict = strict;
        this.cache = cache;
    }

    public Map<String, ParsedSentence> getCache() {
        return cache;
    }

    public Module getModule() {
        return module;
    }

    public boolean isStrict() {
        return strict;
    }

    public static class ParsedSentence implements Serializable {
        private K parse;
        private final Set<KEMException> warnings;

        public ParsedSentence(K parse, Set<KEMException> warnings) {
            this.parse = parse;
            this.warnings = warnings;
        }

        public K getParse() {
            return parse;
        }

        public Set<KEMException> getWarnings() {
            return warnings;
        }
    }
}
