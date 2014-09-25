// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;

import java.util.HashMap;
import java.util.Map;

public class SearchResult {
    private KRunState state;
    /**
    The pretty-printed substitution mapping variables explicitly named in the search pattern to
    their bindings.
    */
    private Map<String, Term> substitution;

    /**
    The raw substitution underlying the search result. Contains all variable bindings, including
    anonymous variables, and is not modified for pretty-printing, but instead suitable for further
    rewriting.
    */
    private Map<String, Term> rawSubstitution;
    private Context context;
    private RuleCompilerSteps compilationInfo;

    public SearchResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo, Context context) {
        this.state = state;
        this.rawSubstitution = rawSubstitution;
        this.context = context;
        this.compilationInfo = compilationInfo;
    }

    public Map<String, Term> getSubstitution() {
        if (substitution == null) {
            substitution = new HashMap<String, Term>();
            for (Variable var : compilationInfo.getVars()) {
                Term rawValue;

                rawValue = rawSubstitution.get(var.getName());

                substitution.put(var.toString(), KRunState.concretize(rawValue, context));
            }
        }
        return substitution;
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
