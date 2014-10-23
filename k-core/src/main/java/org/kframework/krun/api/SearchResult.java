// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import java.util.Map;

public class SearchResult {
    private KRunState state;

    /**
    The raw substitution underlying the search result. Contains all variable bindings, including
    anonymous variables, and is not modified for pretty-printing, but instead suitable for further
    rewriting.
    */
    private Map<String, Term> rawSubstitution;
    private RuleCompilerSteps compilationInfo;

    public SearchResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo) {
        this.state = state;
        this.rawSubstitution = rawSubstitution;
        this.compilationInfo = compilationInfo;
    }

    public Map<String, Term> getRawSubstitution() {
        return rawSubstitution;
    }

    public RuleCompilerSteps getCompilationInfo() {
        return compilationInfo;
    }

    public KRunState getState() {
        return state;
    }
}
