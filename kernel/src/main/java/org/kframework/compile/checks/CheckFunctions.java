// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.compile.RewriteAwareVisitor;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.RuleOrClaim;
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
    private final boolean isSymbolic;

    public CheckFunctions(Set<KEMException> errors, Module m, boolean isSymbolic) {
        this.errors = errors;
        this.m = m;
        this.isSymbolic = isSymbolic;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof RuleOrClaim) {
            RuleOrClaim rl = (RuleOrClaim) sentence;
            check(rl.body());
        } else if (sentence instanceof Context) {
            Context ctx = (Context) sentence;
            check(ctx.body());
        } else if (sentence instanceof ContextAlias) {
            ContextAlias ctx = (ContextAlias) sentence;
            check(ctx.body());
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
                String hook = attributes.getOptional("hook").orElse("");
                if (!isSymbolic && attributes.contains("function")
                    && isLHS()
                    && !atTop
                    && !(hook.equals("SET.element") || hook.equals("SET.concat")
                      || hook.equals("SET.unit") || hook.equals("LIST.element")
                      || hook.equals("LIST.concat") || hook.equals("LIST.unit")
                      || hook.equals("MAP.element") || hook.equals("MAP.concat")
                      || hook.equals("MAP.unit"))) {
                  errors.add(KEMException.compilerError("Illegal function symbol on LHS of rule.", k));
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
}
