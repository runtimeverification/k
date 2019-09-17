// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class GuardOrPatterns {

    private Set<KVariable> vars = new HashSet<>();
    private final boolean kore;

    public GuardOrPatterns(boolean kore) {
      this.kore = kore;
    }

    void resetVars() {
        vars.clear();
    }

    private Rule resolve(Module m, Rule rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        return new Rule(
                transform(rule.body(), m),
                transform(rule.requires(), m),
                transform(rule.ensures(), m),
                rule.att());
    }

    private Context resolve(Module m, Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new Context(
                transform(context.body(), m),
                transform(context.requires(), m),
                context.att());
    }

    public K resolveK(Module m, K k) {
        resetVars();;
        gatherVars(k);
        return transform(k, m);
    }

    public synchronized Sentence resolve(Module m, Sentence s) {
        if (s instanceof Rule) {
            return resolve(m, (Rule) s);
        } else if (s instanceof Context) {
            return resolve(m, (Context) s);
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

    K transform(K term, Module m) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
              if (k.klabel().equals(KLabels.ML_OR)) {
                if (kore) {
                  AddSortInjections inj = new AddSortInjections(m);
                  return KAs(k, newDotVariable(inj.sort(k, Sorts.K())));
                } else {
                  return KAs(k, newDotVariable(k.items().get(1).att().get(Production.class).sort()));
                }
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
    KVariable newDotVariable(Sort s) {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++), Att().add("anonymous").add(Sort.class, s));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }
}
