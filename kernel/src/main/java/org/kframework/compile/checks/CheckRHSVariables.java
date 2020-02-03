// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import com.google.common.collect.Sets;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.compile.GatherVarsVisitor;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;

import java.util.HashSet;
import java.util.Set;

/**
 * Checks a sentence to determine if it declares any variables in the RHS that are not bound in the LHS.
 *
 * More specifically, it performs the following checks: for each anonymous variable, if it is on the right hand side
 * of a rewrite operator, and does not signify a fresh variable or constant, it is an error. For each non-anonymous
 * variable, if it is on the right hand side of a rewrite operator, it is an error if it does not appear anywhere on the
 * left hand side of the rule, and does not signify a fresh variable or constant.
 *
 * Exception: this check takes into account the {@code Attribute.UNBOUND_VARIABLES_KEY} attribute and allows the
 * variables whose names are specified by the attribute to be unbound in the LHS.
 */
public class CheckRHSVariables {
    private final Set<KEMException> errors;

    public CheckRHSVariables(Set<KEMException> errors) {
        this.errors = errors;
    }
    private void check(Rule rule) {
        resetVars();
        Set<String> unboundVariableNames = getUnboundVarNames(rule);
        gatherVars(true, rule.body());
        gatherVars(false, rule.requires());
        gatherVars(false, rule.ensures());
        check(rule.body(), true, unboundVariableNames);
        check(rule.requires(), false, unboundVariableNames);
        check(rule.ensures(), false, unboundVariableNames);
    }

    private void check(Context context) {
        resetVars();
        gatherVars(true, context.body());
        gatherVars(false, context.requires());
        check(context.body(), true, new HashSet<>());
        check(context.requires(), false, new HashSet<>());
    }

    public void check(Sentence s) {
        if (s instanceof Rule) {
            check((Rule) s);
        } else if (s instanceof Context) {
            check((Context) s);
        }
    }

    private Set<String> getUnboundVarNames(Rule rule) {
        Option<String> unboundVariablesString = rule.att().getOption(Attribute.UNBOUND_VARIABLES_KEY);
        Set<String> unboundVariableNames = new HashSet<>();
        if (unboundVariablesString.nonEmpty()) {
            String[] components = unboundVariablesString.get().split(",");
            for (String component : components) {
                unboundVariableNames.add(component.trim());
            }
        }
        return unboundVariableNames;
    }

    private Set<KVariable> vars = Sets.newHashSet();

    void resetVars() {
        vars.clear();
    }

    void gatherVars(boolean isBody, K term) {
        new GatherVarsVisitor(isBody, errors, vars).apply(term);
    }

    private void check(K body, boolean isBody, Set<String> unboundVarNames) {
        Set<KVariable> unbound = new HashSet<>();
        new ComputeUnboundVariables(isBody, errors, vars, unbound::add).apply(body);
        for (KVariable k : unbound) {
            if (unboundVarNames.contains(k.name())) continue;
            errors.add(KEMException.compilerError("Found variable " + k.name()
                + " on right hand side of rule, not bound on left hand side."
                + " Did you mean \"?" + k.name() + "\"?", k));
        }
    }

}
