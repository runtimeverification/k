package org.kframework.kore.compile.checks;

import com.google.common.collect.Sets;
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
        if (rule.att().contains("unblock"))
            return;
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        check(rule.body());
        check(rule.requires());
        check(rule.ensures());
    }

    private void check(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        check(context.body());
        check(context.requires());
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
        new RewriteAwareVisitor() {
            @Override
            public Void apply(KVariable v) {
                if (isLHS() && !v.equals(ResolveAnonVar.ANON_VAR))
                    vars.add(v);
                return super.apply(v);
            }

            @Override
            public Void apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                return super.apply(k);
            }

            @Override
            public Void apply(InjectedKLabel k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private void check(K body) {
        new RewriteAwareVisitor() {
            @Override
            public Void apply(KVariable k) {
                if (isRHS()) {
                    if ((k.equals(ResolveAnonVar.ANON_VAR) && !isLHS())
                        || (!k.equals(ResolveAnonVar.ANON_VAR) && !(k.name().startsWith("?") || k.name().startsWith("!")) && !vars.contains(k))) {
                        errors.add(KEMException.compilerError("Found variable " + k.name()
                                + " on right hand side of rule, not bound on left hand side."
                                + " Did you mean \"?" + k.name() + "\"?", k));
                    }
                }
                return null;
            }

            @Override
            public Void apply(InjectedKLabel k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                return super.apply(k);
            }

            @Override
            public Void apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    apply((KVariable) k.klabel());
                }
                return super.apply(k);
            }
        }.apply(body);
    }
}
