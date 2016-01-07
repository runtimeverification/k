// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.kore.compile.checks;

import com.google.common.collect.Sets;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.ResolveAnonVar;
import org.kframework.kore.compile.RewriteAwareVisitor;
import org.kframework.utils.errorsystem.KEMException;

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
        gatherVars(rule.body());
        check(rule.body(), true);
        check(rule.requires(), false);
        check(rule.ensures(), false);
    }

    private void check(Context context) {
        resetVars();
        gatherVars(context.body());
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

    void gatherVars(K term) {
        new RewriteAwareVisitor(true) {
            @Override
            public void apply(KVariable v) {
                if (isLHS() && !v.equals(ResolveAnonVar.ANON_VAR))
                    vars.add(v);
                super.apply(v);
            }

            @Override
            public void apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                super.apply(k);
            }

            @Override
            public void apply(InjectedKLabel k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                super.apply(k);
            }
        }.apply(term);
    }

    private void check(K body, boolean isBody) {
        new RewriteAwareVisitor(isBody) {
            @Override
            public void apply(KVariable k) {
                if (isRHS()) {
                    if (!k.name().equals(KLabels.THIS_CONFIGURATION) &&
                            ((k.equals(ResolveAnonVar.ANON_VAR) && !isLHS())
                        || (!k.equals(ResolveAnonVar.ANON_VAR) && !(k.name().startsWith("?") || k.name().startsWith("!")) && !vars.contains(k)))) {
                        errors.add(KEMException.compilerError("Found variable " + k.name()
                                + " on right hand side of rule, not bound on left hand side."
                                + " Did you mean \"?" + k.name() + "\"?", k));
                    }
                }
            }

            @Override
            public void apply(InjectedKLabel k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                super.apply(k);
            }

            @Override
            public void apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                super.apply(k);
            }
        }.apply(body);
    }
}
