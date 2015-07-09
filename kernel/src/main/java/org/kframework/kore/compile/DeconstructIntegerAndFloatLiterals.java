// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Transforms patterns in the LHS of rules which have tokens of sort Int or Float
 * into side conditions generating equality over a reconstructed value.
 * Thus,
 *
 * rule 5 => .K
 *
 * becomes
 *
 * rule I:Int => .K when I ==K 5
 */
public class DeconstructIntegerAndFloatLiterals {

    private Set<KApply> state = new HashSet<>();
    private Set<KVariable> vars = new HashSet<>();

    void reset() {
        state.clear();
        vars.clear();
    }

    void gatherVars(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KVariable v) {
                vars.add(v);
                return super.apply(v);
            }
        }.apply(term);
    }

    public Sentence convert(Sentence s) {
        if (s instanceof Rule) {
            return convert((Rule) s);
        } else if (s instanceof Context) {
            return convert((Context) s);
        } else {
            return s;
        }
    }

    private Rule convert(Rule rule) {
        reset();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        K body = convert(rule.body());
        return Rule(
                body,
                addSideCondition(rule.requires()),
                rule.ensures(),
                rule.att());
    }

    private Context convert(Context context) {
        reset();
        gatherVars(context.body());
        gatherVars(context.requires());
        K body = convert(context.body());
        return Context(
                body,
                addSideCondition(context.requires()),
                context.att());
    }

    private int counter = 0;
    KVariable newDotVariable() {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

    K addSideCondition(K requires) {
        Optional<KApply> sideCondition = state.stream().reduce(BooleanUtils::and);
        if (!sideCondition.isPresent()) {
            return requires;
        } else if (requires.equals(BooleanUtils.TRUE) && sideCondition.isPresent()) {
            return sideCondition.get();
        } else {
            return BooleanUtils.and(requires, sideCondition.get());
        }
    }

    private K convert(K term) {
        return new TransformKORE() {

            @Override
            public K apply(KToken k) {
                if (rhsOf == null) {
                    //lhs
                    if (k.sort().equals(Sorts.Int()) || k.sort().equals(Sorts.Float())) {
                        KVariable var = newDotVariable();
                        state.add(KApply(KLabel("_==K_"), var, k));
                        return var;
                    }
                }
                return super.apply(k);
            }

            private K rhsOf;

            @Override
            public K apply(KRewrite k) {
                K l = apply(k.left());
                rhsOf = k;
                K r = apply(k.right());
                rhsOf = null;
                if (l != k.left() || r != k.right()) {
                    return KRewrite(l, r, k.att());
                } else {
                    return k;
                }
            }
        }.apply(term);
    }

}
