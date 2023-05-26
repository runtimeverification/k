// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.compile.RewriteAwareVisitor;
import org.kframework.definition.Claim;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Check that functions are not used on LHS in places that should be performing matching.
 */
public class CheckFunctions {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckFunctions(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            Rule rl = (Rule) sentence;
            checkFuncAtt(rl);
            if (!rl.att().contains(Att.SIMPLIFICATION()))
                // functions are allowed on the LHS of simplification rules
                check(rl.body());
        } else if (sentence instanceof Claim) {
            // functions are allowed on LHS of claims
            Claim c = (Claim) sentence;
            if (c.att().contains(Att.MACRO()) || c.att().contains(Att.MACRO_REC())
                    || c.att().contains(Att.ALIAS()) || c.att().contains(Att.ALIAS_REC()))
                errors.add(KEMException.compilerError(
                        "Attributes " + Att.MACRO() + "|" + Att.MACRO_REC() + "|"
                                + Att.ALIAS() + "|" + Att.ALIAS_REC() + " are not allowed on claims.", c));
        } else if (sentence instanceof Context) {
            Context ctx = (Context) sentence;
            check(ctx.body());
            if (ctx.att().contains(Att.MACRO()) || ctx.att().contains(Att.MACRO_REC())
                    || ctx.att().contains(Att.ALIAS()) || ctx.att().contains(Att.ALIAS_REC()))
                errors.add(KEMException.compilerError(
                        "Attributes " + Att.MACRO() + "|" + Att.MACRO_REC() + "|"
                                + Att.ALIAS() + "|" + Att.ALIAS_REC() + " are not allowed on contexts.", ctx));
        } else if (sentence instanceof ContextAlias) {
            ContextAlias ctx = (ContextAlias) sentence;
            check(ctx.body());
            if (ctx.att().contains(Att.MACRO()) || ctx.att().contains(Att.MACRO_REC())
                    || ctx.att().contains(Att.ALIAS()) || ctx.att().contains(Att.ALIAS_REC()))
                errors.add(KEMException.compilerError(
                        "Attributes " + Att.MACRO() + "|" + Att.MACRO_REC() + "|"
                                + Att.ALIAS() + "|" + Att.ALIAS_REC() + " are not allowed on contexts.", ctx));
        }
    }

    public void check(K body) {
        new RewriteAwareVisitor(true, errors) {
            boolean atTop = true;
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("#withConfig")) {
                  super.apply(k);
                  return;
                }
                if (k.klabel() instanceof KVariable || CheckKLabels.isInternalKLabel(k.klabel().name(), m) || !m.attributesFor().contains(k.klabel()) ) {
                  atTop  = false;
                  super.apply(k);
                  return;
                }
                Att attributes = m.attributesFor().apply(k.klabel());
                String hook = attributes.getOptional(Att.HOOK()).orElse("");
                if (attributes.contains(Att.FUNCTION())
                    && isLHS()
                    && !atTop
                    && !(hook.equals("LIST.element") || hook.equals("LIST.concat") || hook.equals("LIST.unit")
                      || hook.equals("SET.element") || hook.equals("SET.concat") || hook.equals("SET.unit")
                      || hook.equals("MAP.element") || hook.equals("MAP.concat") || hook.equals("MAP.unit")
                      || hook.equals("BAG.element") || hook.equals("BAG.concat") || hook.equals("BAG.unit"))) {
                  errors.add(KEMException.compilerError("Illegal function symbol " + k.klabel().name() + " on LHS of rule." +
                          " Consider adding `simplification` attribute to the rule if this is intended.", k));
                }
                atTop = false;
                if (hook.equals("SET.element")) return;
                if (hook.equals("MAP.element")) {
                  apply(k.items().get(1));
                  return;
                }
                super.apply(k);
            }
        }.apply(body);
    }

    public void checkFuncAtt(Rule r) {
        new RewriteAwareVisitor(true, errors) {
            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals("#withConfig")) {
                    super.apply(k);
                    return;
                }
                if ((isRHS() && !isLHS()) || k.klabel() instanceof KVariable || !m.attributesFor().contains(k.klabel())) {
                    return;
                }
                Att attributes = m.attributesFor().apply(k.klabel());
                if (attributes.contains(Att.FUNCTION()) && (r.att().contains(Att.MACRO())
                                                     || r.att().contains(Att.MACRO_REC())
                                                     || r.att().contains(Att.ALIAS())
                                                     || r.att().contains(Att.ALIAS_REC()))) {
                    errors.add(KEMException.compilerError(
                            "Attributes " + Att.MACRO() + "|" + Att.MACRO_REC() + "|"
                                    + Att.ALIAS() + "|" + Att.ALIAS_REC() + " are not allowed on function rules.", r));
                }
            }
        }.apply(r.body());
    }
}
