// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.KLabels;
import org.kframework.definition.Context;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class GuardOrPatterns {

    private Set<KVariable> vars = new HashSet<>();

    void resetVars() {
        vars.clear();
    }

    private Rule resolve(Rule rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        return new Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private Context resolve(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public K resolveK(K k) {
        resetVars();;
        gatherVars(k);
        return transform(k);
    }

    public synchronized Sentence resolve(Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else {
            return s;
        }
    }

    void gatherVars(K term) {
        new VisitK() {
            @Override
            public void apply(KVariable v) {
                vars.add(v);
                super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
              if (k.klabel().equals(KLabels.ML_OR)) {
                return KAs(k, newDotVariable());
              }
              return super.apply(k);
            }

            @Override
            public K apply(KAs k) {
              return k;
            }

            @Override
            public K apply(KRewrite k) {
              return KRewrite(k.left(), apply(k.right()), k.att());
            }
        }.apply(term);
    }

    private int counter = 0;
    KVariable newDotVariable() {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++), Att().add("anonymous"));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }
}
