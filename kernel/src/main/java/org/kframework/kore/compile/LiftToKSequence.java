// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KSequence;

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
        K result = new TransformKORE()  {
            @Override
            public K apply(KApply k) {
                List<K> children = new ArrayList<>();
                for (K child : k.klist().items()) {
                    K res = apply(child);
                    if (res instanceof KSequence) {
                        children.add(res);
                    } else {
                        children.add(KSequence(res));
                    }
                }
                return KApply(k.klabel(), KList(children), k.att());
            }
        }.apply(term);
        if (result instanceof KSequence) {
            return result;
        } else {
            return KSequence(result);
        }
    }

    public K lower(K term) {
        return new TransformKORE() {
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
