// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KSequence;
import org.kframework.kore.KVariable;
import org.kframework.kore.FoldK;

public class AddCoolLikeAtt {

    private final Module mod;

    public AddCoolLikeAtt(Module mod) {
      this.mod = mod;
    }

    private Rule add(Rule rule) {
        return new Rule(
                rule.body(),
                rule.requires(),
                rule.ensures(),
                transform(rule.body(), rule.att()));
    }

    private Context add(Context context) {
        return new Context(
                context.body(),
                context.requires(),
                transform(context.body(), context.att()));
    }

    private ContextAlias add(ContextAlias context) {
        return new ContextAlias(
                context.body(),
                context.requires(),
                transform(context.body(), context.att()));
    }

    private Att transform(K body, Att att) {
        if (new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return false;
            }

            @Override
            public Boolean apply(KApply k) {
                if (mod.attributesFor().get(k.klabel()).getOrElse(() -> Att.empty()).contains("maincell")) {
                    if (k.items().get(0) instanceof KSequence) {
                        KSequence seq = (KSequence) k.items().get(0);
                        if (seq.items().get(0) instanceof KVariable) {
                            return true;
                        }
                    }
                }
                return super.apply(k);
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }
        }.apply(body)) {
          return att.add("cool-like");
        }
        return att;
    }

    public synchronized Sentence add(Sentence s) {
        if (s instanceof Rule) {
            return add((Rule) s);
        } else if (s instanceof Context) {
            return add((Context) s);
        } else if (s instanceof ContextAlias) {
            return add((ContextAlias) s);
        } else {
            return s;
        }
    }
}
