// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ResolveStrict;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class CheckHOLE {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckHOLE(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Production) {
            check((Production) sentence);
        } else if (sentence instanceof Context) {
            check((Context) sentence);
        }
    }

    private void check(Production prod) {
        if (prod.att().contains(Att.STRICT())) {
            check(prod, prod.att().get(Att.STRICT()));
        }
        if (prod.att().contains(Att.SEQSTRICT())) {
            check(prod, prod.att().get(Att.SEQSTRICT()));
        }
    }

    private void check(Production prod, String att) {
        long arity = prod.nonterminals().size();
        List<Integer> strictnessPositions = new ArrayList<>();
        if (att.isEmpty()) {
            for (int i = 1; i <= arity; i++) {
                strictnessPositions.add(i);
            }
        } else {
            try {
                String[] components = att.split(";");
                if (components.length == 1) {
                    if (Character.isDigit(components[0].trim().charAt(0))) {
                        ResolveStrict.setPositions(components[0].trim(), strictnessPositions, arity, prod);
                    } else {
                        for (int i = 1; i <= arity; i++) {
                            strictnessPositions.add(i);
                        }
                    }
                } else if (components.length % 2 == 0) {
                    for (int i = 0; i < components.length; i += 2) {
                        ResolveStrict.setPositions(components[i+1].trim(), strictnessPositions, arity, prod);
                    }
                } else {
                    errors.add(KEMException.compilerError("Invalid strict attribute containing invalid semicolons. Must contain 0, 1, 2, or an even number of components.", prod));
                }
            } catch (KEMException e) {
                errors.add(e);
            }
        }
        for (int pos : strictnessPositions) {
            if (prod.nonterminals().apply(pos-1).sort().equals(Sorts.K())) {
                errors.add(KEMException.compilerError("Cannot heat a nonterminal of sort K. Did you mean KItem?", prod));
            }
        }
    }

    private static final KApply K_HOLE = KApply(KLabel("#SemanticCastToK"), KVariable("HOLE"));

    private void check(Context ctx) {
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (k.equals(K_HOLE)) {
                    errors.add(KEMException.compilerError("Cannot heat a HOLE of sort K. Did you mean to sort it to KItem?", k));
                }
                super.apply(k);
            }
        }.apply(ctx.body());
    }
}
