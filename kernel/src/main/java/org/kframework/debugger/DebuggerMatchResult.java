// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;

import java.util.List;
import java.util.Map;

/**
 * Created by Manasvi on 8/19/15.
 * Represents the result of a match on a configuration
 */
public class DebuggerMatchResult {
    private final List<? extends Map<? extends KVariable, ? extends K>> substitutions;
    private final Rule parsedRule;
    private final Rule compiledRule;
    private final String pattern;

    public DebuggerMatchResult(List<? extends Map<? extends KVariable, ? extends K>> substitutions, Rule parsedRule, Rule compiledRule, String pattern) {
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

    public List<? extends Map<? extends KVariable, ?extends K>> getSubstitutions() {
        return substitutions;
    }

    public String getPattern() {
        return pattern;
    }
}

