// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class used by KRun to compile patterns used for the search command.
 * Performs most rule-related transformation.  It is expected to be called on a
 * {@link org.kframework.kil.Rule} which contains the pattern as its body and
 * constraints on the pattern as its requires condition.
 */
public class RuleCompilerSteps extends CompilerSteps<Rule> {

    private Set<Variable> vars;

    /**
     * Used in the search process to compute the substitution to be displayed
     * for a given solution
     * @return the set of named {@link org.kframework.kil.Variable}s contained by the pattern
     */
    public Set<Variable> getVars() {
        return vars;
    }

    public RuleCompilerSteps(Context context) {
        super(context);
        this.add(new AddKCell(context));
        this.add(new AddTopCellRules(context));
        this.add(new ResolveAnonymousVariables(context));
        this.add(new ResolveSyntaxPredicates(context));
        this.add(new ResolveListOfK(context));
        this.add(new FlattenTerms(context));
        final ResolveContextAbstraction resolveContextAbstraction =
                new ResolveContextAbstraction(context);
        this.add(resolveContextAbstraction);
        this.add(new ResolveOpenCells(context));
        this.add(new CompileDataStructures(context, true));
    }

    @Override
    public Rule compile(Rule def, String stepName) throws CompilerStepDone {
        CollectVariablesVisitor collectVars = new CollectVariablesVisitor(context);
        collectVars.visitNode(def);
        vars = new HashSet<Variable>();
        for (List<Variable> collectedVars : collectVars.getVars().values()) {
            vars.add(collectedVars.get(0));
        }
        return super.compile(def, stepName);
    }
}
