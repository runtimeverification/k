// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.HashSet;
import java.util.Set;

/**
 * Class used by KRun to compile patterns used for the search command.
 * Performs most rule-related transformation.  It is expected to be called on a
 * {@link org.kframework.kil.Rule} which contains the pattern as its body and
 * constraints on the pattern as its requires condition.
 */
public class RuleCompilerSteps extends CompilerSteps<Rule> {

    private Set<Variable> vars;
    private Set<Variable> rawVars;

    /**
     * Used in the search process to compute the substitution to be displayed
     * for a given solution
     * @return the set of named {@link org.kframework.kil.Variable}s contained by the pattern
     */
    public Set<Variable> getVars() {
        return vars;
    }

    public Variable getVar(String name) {
        // The backend doesn't keep sort information around so we want to
        // match the variable name only.
        for (Variable var : rawVars) {
            if (name.equals(var.getName())) {
                return var;
            }
        }
        return null;
    }

    public RuleCompilerSteps(Context context, KExceptionManager kem) {
        super(context);
        this.add(new AddKCell(context));
        this.add(new AddTopCellRules(context));
        this.add(new ResolveAnonymousVariables(context));
        this.add(new ResolveSyntaxPredicates(context));
        this.add(new ResolveListOfK(context));
        this.add(new FlattenTerms(context));
        final ResolveContextAbstraction resolveContextAbstraction =
                new ResolveContextAbstraction(context, kem);
        this.add(resolveContextAbstraction);
        this.add(new ResolveOpenCells(context));
        this.add(new Cell2DataStructure(context));
        this.add(new CompileDataStructures(context, kem));
    }

    @Override
    public Rule compile(Rule def, String stepName) throws CompilerStepDone {
        vars = new HashSet<>();
        addVarsOfRule(def, vars);
        rawVars = new HashSet<>();
        def = super.compile(def, stepName);
        addVarsOfRule(def, rawVars);
        return def;
    }

    private void addVarsOfRule(Rule def, Set<Variable> vars) {
        vars.addAll(def.getBody().variables());
        if (def.getRequires() != null)
            vars.addAll(def.getRequires().variables());
        if (def.getEnsures() != null)
            vars.addAll(def.getEnsures().variables());
    }
}
