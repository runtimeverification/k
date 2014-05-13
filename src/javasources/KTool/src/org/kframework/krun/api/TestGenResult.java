// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import java.util.Map;

public class TestGenResult extends SearchResult{

    private Term generatedProgram;
    private SymbolicConstraint constraint;

    public Term getGeneratedProgram() {
        return generatedProgram;
    }

    public SymbolicConstraint getConstraint() {
        return constraint;
    }

    public TestGenResult(KRunState state,
                         Map<String, Term> rawSubstitution,
                         RuleCompilerSteps compilationInfo,
                         Context context, Term program,
                         SymbolicConstraint constraint) {
        super(state,rawSubstitution,compilationInfo,context);
        this.generatedProgram = program;
        this.constraint = constraint;
    }
}