// Copyright (c) 2016-2018 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Created by dwightguth on 1/25/16.
 */
public class CheckRewrite {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckRewrite(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            check(((Rule) sentence).body());
        }
    }

    private void check(K body) {
        class Holder {
            boolean hasRewrite = false;
            boolean inRewrite = false;
        }
        Holder h = new Holder();
        new VisitK() {
            @Override
            public void apply(KRewrite k) {
                boolean inRewrite = h.inRewrite;
                if (h.inRewrite) {
                    errors.add(KEMException.compilerError("Rewrites are not allowed to be nested.", k));
                }
                h.hasRewrite = true;
                h.inRewrite = true;
                super.apply(k);
                h.inRewrite = inRewrite;
            }

            @Override
            public void apply(KApply k) {
                if (!(k.klabel() instanceof KVariable) && k.klabel().name().equals("#fun2") || k.klabel().name().equals("#fun3")) {
                    if (k.klabel().name().equals("#fun2")) {
                        boolean wasInRewrite = h.inRewrite;
                        boolean hadRewrite = h.hasRewrite;
                        h.inRewrite = false;
                        h.hasRewrite = false;
                        apply(k.items().get(0));
                        if (!h.hasRewrite) {
                            errors.add(KEMException.compilerError("#fun expressions must have at least one rewrite.", k));
                        }
                        // in well formed programs this should always reset to true and true, but we want to make sure we
                        // don't create spurious reports if this constraint was violated by the user.
                        h.inRewrite = wasInRewrite;
                        h.hasRewrite = hadRewrite;
                        apply(k.items().get(1));
                    } else {
                        boolean wasInRewrite = h.inRewrite;
                        boolean hadRewrite = h.hasRewrite;
                        h.inRewrite = true;
                        h.hasRewrite = true;
                        apply(k.items().get(0));
                        apply(k.items().get(1));
                        // in well formed programs this should always reset to true and true, but we want to make sure we
                        // don't create spurious reports if this constraint was violated by the user.
                        h.inRewrite = wasInRewrite;
                        h.hasRewrite = hadRewrite;
                        apply(k.items().get(2));
                    }
                } else {
                    super.apply(k);
                }
            }
        }.accept(body);
        if (!h.hasRewrite) {
            errors.add(KEMException.compilerError("Rules must have at least one rewrite.", body));
        }
    }
}
