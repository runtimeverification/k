package org.kframework.krun.api;

import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.Map;

/**
 * Created with IntelliJ IDEA.
 * User: owolabi
 * Date: 8/2/13
 * Time: 1:57 AM
 * To change this template use File | Settings | File Templates.
 */
public class GeneratorResult extends SearchResult{

    public Term getGeneratedProgram() {
        return generatedProgram;
    }

    private Term generatedProgram;

    public GeneratorResult(KRunState state, Map<String, Term> rawSubstitution, RuleCompilerSteps compilationInfo, Context context, Term program) {
        super(state,rawSubstitution,compilationInfo,context);
        this.generatedProgram = program;
    }


}

