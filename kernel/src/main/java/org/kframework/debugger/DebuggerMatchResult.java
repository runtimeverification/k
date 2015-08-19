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
    private final List<Map<KVariable, K>> substitutions;
    private final Rule parsedRule;
    private final Rule compiledRule;

    public DebuggerMatchResult(List<Map<KVariable, K>> substitutions, Rule parsedRule, Rule compiledRule) {
        this.substitutions = substitutions;
        this.parsedRule = parsedRule;
        this.compiledRule = compiledRule;
    }

    public Rule getCompiledRule() {
        return compiledRule;
    }

    public Rule getParsedRule() {
        return parsedRule;
    }

    public List<Map<KVariable, K>> getSubstitutions() {
        return substitutions;
    }
}
