package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import java.util.Map;

public class TestGenResult extends SearchResult{

    private Term generatedProgram;

    public Term getGeneratedProgram() {
        return generatedProgram;
    }

    public TestGenResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo, Context context, Term program) {
        super(state,rawSubstitution,compilationInfo,context);
        this.generatedProgram = program;
    }
}