// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.Sorts;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.ArrayList;
import java.util.List;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Raises all rules into a form with a KSequence in every position that expects a term of sort K.
 */
public class LiftToKSequence {


    public Sentence lift(Sentence s) {
        if (s instanceof Rule) {
            return lift((Rule) s);
        } else if (s instanceof Context) {
            return lift((Context) s);
        } else {
            return s;
        }
    }

    private Rule lift(Rule rule) {
        return Rule(
                lift(rule.body()),
                lift(rule.requires()),
                lift(rule.ensures()),
                rule.att());
    }

    private Context lift(Context context) {
        return Context(
                lift(context.body()),
                lift(context.requires()),
                context.att());
    }

    public K lift(K term) {
        K result = new TransformK()  {
            @Override
            public K apply(KApply k) {
                List<K> children = new ArrayList<>();
                for (K child : k.klist().items()) {
                    K res = apply(child);
                    if (res instanceof KSequence || k.klabel().equals(KLabels.ML_OR)) {
                        children.add(res);
                    } else {
                        children.add(KSequence(res));
                    }
                }
                return KApply(k.klabel(), KList(children), k.att());
            }

            @Override
            public K apply(KAs k) {
                K res = apply(k.pattern());
                KVariable var = (KVariable) k.alias();
                if (!(res instanceof KSequence) && var.att().getOptional(Sort.class).orElse(Sorts.K()).equals(Sorts.K())) {
                    res = KSequence(res);
                }
                return KAs(res, k.alias(), k.att());
            }
        }.apply(term);
        if (result instanceof KSequence) {
            return result;
        } else {
            return KSequence(result);
        }
    }

    public K lower(K term) {
        return new TransformK() {
            @Override
            public K apply(KSequence k) {
                if (k.items().size() == 1) {
                    return super.apply(k.items().get(0));
                }
                return super.apply(k);
            }
        }.apply(term);
    }
}
