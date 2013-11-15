package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.SymbolicUnifier;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * @author: AndreiS
 */
public class MetaK {

    public static BoolToken unifiable(Term term1, Term term2, TermContext context) {
//        Term freshTerm1 = term1.substitute(Variable.getFreshSubstitution(term1.variableSet()), context);
//        Term freshTerm2 = term2.substitute(Variable.getFreshSubstitution(term2.variableSet()), context);
        SymbolicConstraint constraint = new SymbolicConstraint(context);
        SymbolicUnifier unifier = new SymbolicUnifier(constraint, context);
        try {
            unifier.unify(term1, term2);
        } catch (MatcherException e) {
            return BoolToken.FALSE;
        }
        return BoolToken.TRUE;
    }

    public static Term rename(Term term, BuiltinSet builtinSet, TermContext context) {
        if (builtinSet.hasFrame() /* || !builtinSet.operations().isEmpty() */) {
            return term;
        }

        Set<Variable> variables = new HashSet<Variable>();
        for (Term element : builtinSet.elements()) {
            if (!(element instanceof MetaVariable)) {
                return term;
            }

            variables.add(new Variable((MetaVariable) element));
        }

        return term.substitute(Variable.getFreshSubstitution(variables), context);
    }

    public static Term renameVariables(Term term, TermContext context) {
        Set<Variable> variables = term.variableSet();
        return term.substitute(Variable.getFreshSubstitution(variables), context);
    }

    public static BuiltinSet variables(Term term, TermContext context) {
        Set<Term> metaVariables = new HashSet<Term>();
        for (Variable variable : term.variableSet()) {
            metaVariables.add(new MetaVariable(variable));
        }
        return new BuiltinSet(metaVariables);
    }

    public static BuiltinMap variablesMap(BuiltinSet variableSet, TermContext context) {
        Set<Term> variables = variableSet.elements();
        Map<MetaVariable, Variable> result = new HashMap<>(variables.size());
        for (Term variable : variables) {
            assert variable instanceof MetaVariable : "this function only applies on metavariables";
            result.put((MetaVariable) variable, ((MetaVariable) variable).variable());
        }
        return BuiltinMap.of(result, null);
    }

    public static Term ite(BoolToken boolToken, Term t, Term e, TermContext context) {
        if (boolToken.booleanValue()) return t;
        return e;
    }

}
