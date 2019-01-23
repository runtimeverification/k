// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import com.google.common.collect.Sets;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.compile.GatherVarsVisitor;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;

/**
 * Checks a sentence to determine if it declares any variables in the RHS that are not bound in the LHS.
 *
 * More specifically, it performs the following checks: for each anonymous variable, if it is on the right hand side
 * of a rewrite operator, and does not signify a fresh variable or constant, it is an error. For each non-anonymous
 * variable, if it is on the right hand side of a rewrite operator, it is an error if it does not appear anywhere on the
 * left hand side of the rule, and does not signify a fresh variable or constant.
 */
public class CheckRHSVariables {
    private final Set<KEMException> errors;

    public CheckRHSVariables(Set<KEMException> errors) {
        this.errors = errors;
    }
    private void check(Rule rule) {
        resetVars();
        gatherVars(true, rule.body());
        gatherVars(false, rule.requires());
        gatherVars(false, rule.ensures());
        check(rule.body(), true);
        check(rule.requires(), false);
        check(rule.ensures(), false);
    }

    private void check(Context context) {
        resetVars();
        gatherVars(true, context.body());
        gatherVars(false, context.requires());
        check(context.body(), true);
        check(context.requires(), false);
    }

    public void check(Sentence s) {
        if (s instanceof Rule) {
            check((Rule) s);
        } else if (s instanceof Context) {
            check((Context) s);
        }
    }

    private Set<KVariable> vars = Sets.newHashSet();

    void resetVars() {
        vars.clear();
    }

    void gatherVars(boolean isBody, K term) {
        new GatherVarsVisitor(isBody, errors, vars).apply(term);
    }

    private void check(K body, boolean isBody) {
        Set<KVariable> unbound = new HashSet<>();
        new ComputeUnboundVariables(isBody, errors, vars, unbound::add).apply(body);
        for (KVariable k : unbound) {
            errors.add(KEMException.compilerError("Found variable " + k.name()
                + " on right hand side of rule, not bound on left hand side."
                + " Did you mean \"?" + k.name() + "\"?", k));
        }
    }

}
