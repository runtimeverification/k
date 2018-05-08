// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.definition.Rule;
import org.kframework.kore.K;

/**
 * Created by Manasvi on 8/19/15.
 * Represents the result of a match on a configuration
 */
public class DebuggerMatchResult {
    private final K substitutions;
    private final Rule parsedRule;
    private final Rule compiledRule;
    private final String pattern;

    public DebuggerMatchResult(K substitutions, Rule parsedRule, Rule compiledRule, String pattern) {
        this.substitutions = substitutions;
        this.parsedRule = parsedRule;
        this.compiledRule = compiledRule;
        this.pattern = pattern;
    }

    public Rule getCompiledRule() {
        return compiledRule;
    }

    public Rule getParsedRule() {
        return parsedRule;
    }

    public K getSubstitutions() {
        return substitutions;
    }

    public String getPattern() {
        return pattern;
    }
}

