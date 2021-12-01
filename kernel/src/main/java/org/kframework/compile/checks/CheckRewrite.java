// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.Claim;
import org.kframework.definition.Module;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
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
        if (sentence instanceof RuleOrClaim) {
            check((RuleOrClaim) sentence, sentence instanceof Claim);
        }
    }

    private void check(RuleOrClaim sentence, boolean isClaim) {
        class Holder {
            boolean hasRewrite = false;
            boolean inRewrite = false;
            boolean inRewriteRHS = false;
            boolean inAs = false;
            boolean inFunctionContext = false;
            boolean inFunctionBody = false;
        }
        Holder h = new Holder();
        VisitK visitor = new VisitK() {
            @Override
            public void apply(KRewrite k) {
                boolean inRewrite = h.inRewrite;
                boolean inRewriteRHS = h.inRewriteRHS;
                if (h.inRewrite) {
                    errors.add(KEMException.compilerError("Rewrites are not allowed to be nested.", k));
                }
                if (h.inFunctionContext) {
                    errors.add(KEMException.compilerError("Rewrites are not allowed in the context of a function rule.", k));
                }
                if (h.inAs) {
                    errors.add(KEMException.compilerError("Rewrites are not allowed inside an #as pattern.", k));
                }
                h.hasRewrite = true;
                h.inRewrite = true;
                super.apply(k.left());
                h.inRewriteRHS = true;
                super.apply(k.right());
                h.inRewriteRHS = inRewriteRHS;
                h.inRewrite = inRewrite;
            }

            @Override
            public void apply(KAs k) {
                boolean inAs = h.inAs;
                if (h.inRewriteRHS)
                    errors.add(KEMException.compilerError("#as is not allowed in the RHS of a rule.", k));
                h.inAs = true;
                super.apply(k);
                h.inAs = inAs;
            }

            @Override
            public void apply(KVariable k) {
                if (!h.inRewriteRHS && k.name().startsWith("?")) {
                    errors.add(KEMException.compilerError(
                            "Existential variable " + k.name() + " found in LHS. Existential variables are only allowed in the RHS.", k));
                }
            }

            @Override
            public void apply(KApply k) {
                if (!(k.klabel() instanceof KVariable) && k.klabel().name().equals("#fun2") || k.klabel().name().equals("#fun3")) {
                    if (k.klabel().name().equals("#fun2")) {
                        boolean wasInRewrite = h.inRewrite;
                        boolean hadRewrite = h.hasRewrite;
                        boolean wasInFunctionContext = h.inFunctionContext;
                        boolean wasInFunctionBody = h.inFunctionBody;
                        h.inRewrite = false;
                        h.hasRewrite = false;
                        h.inFunctionContext = false;
                        h.inFunctionBody = false;
                        apply(k.items().get(0));
                        if (!h.hasRewrite) {
                            errors.add(KEMException.compilerError("#fun expressions must have at least one rewrite.", k));
                        }
                        // in well formed programs this should always reset to true and true, but we want to make sure we
                        // don't create spurious reports if this constraint was violated by the user.
                        h.inRewrite = wasInRewrite;
                        h.hasRewrite = hadRewrite;
                        h.inFunctionContext = wasInFunctionContext;
                        h.inFunctionBody = wasInFunctionBody;
                        apply(k.items().get(1));
                    } else if (k.klabel().name().equals("#fun3")) {
                        boolean wasInRewrite = h.inRewrite;
                        boolean hadRewrite = h.hasRewrite;
                        boolean wasInFunctionContext = h.inFunctionContext;
                        boolean wasInFunctionBody = h.inFunctionBody;
                        h.inRewrite = true;
                        h.hasRewrite = true;
                        h.inFunctionContext = false;
                        h.inFunctionBody = false;
                        apply(k.items().get(0));
                        apply(k.items().get(1));
                        // in well formed programs this should always reset to true and true, but we want to make sure we
                        // don't create spurious reports if this constraint was violated by the user.
                        h.inRewrite = wasInRewrite;
                        h.hasRewrite = hadRewrite;
                        h.inFunctionContext = wasInFunctionContext;
                        h.inFunctionBody = wasInFunctionBody;
                        apply(k.items().get(2));
                    } else {
                        boolean wasInRewrite = h.inRewrite;
                        boolean hadRewrite = h.hasRewrite;
                        boolean wasInFunctionContext = h.inFunctionContext;
                        boolean wasInFunctionBody = h.inFunctionBody;
                        h.inRewrite = true;
                        h.hasRewrite = true;
                        h.inFunctionContext = false;
                        h.inFunctionBody = false;
                        apply(k.items().get(0));
                        apply(k.items().get(2));
                        // in well formed programs this should always reset to true and true, but we want to make sure we
                        // don't create spurious reports if this constraint was violated by the user.
                        h.inRewrite = wasInRewrite;
                        h.hasRewrite = hadRewrite;
                        h.inFunctionContext = wasInFunctionContext;
                        h.inFunctionBody = wasInFunctionBody;
                        apply(k.items().get(1));
                    }
                } else if (!(k.klabel() instanceof KVariable) && k.klabel().name().equals("#withConfig")) {
                    boolean inFunctionContext = h.inFunctionContext;
                    boolean inFunctionBody = h.inFunctionBody;
                    if (h.inFunctionContext || h.inFunctionBody) {
                        errors.add(KEMException.compilerError("Function context is not allowed to be nested.", k));
                    }
                    if (h.inRewrite) {
                      errors.add(KEMException.compilerError("Function context is not allowed inside a rewrite.", k));
                    }
                    h.inFunctionBody = true;
                    apply(k.items().get(0));
                    h.inFunctionBody = inFunctionBody;
                    h.inFunctionContext = true;
                    apply(k.items().get(1));
                    h.inFunctionContext = inFunctionContext;
                } else {
                    super.apply(k);
                }
            }
        };
        visitor.accept(sentence.requires());
        visitor.accept(sentence.body());
        if (!h.hasRewrite && !isClaim) {
            errors.add(KEMException.compilerError("Rules must have at least one rewrite.", sentence.body()));
        }
    }
}
