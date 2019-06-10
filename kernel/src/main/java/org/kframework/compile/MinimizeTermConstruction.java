// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class MinimizeTermConstruction {

    private final Set<KVariable> vars = new HashSet<>();
    private final Map<K, KVariable> cache = new HashMap<>();
    private final Set<K> usedOnRhs = new HashSet<>();

    private final Module module;

    public MinimizeTermConstruction(Module module) {
        this.module = module;
    }

    void resetVars() {
        vars.clear();
        cache.clear();
        usedOnRhs.clear();
        counter = 0;
    }

    private Rule resolve(Rule rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        gatherTerms(rule.body(), true);
        gatherTerms(rule.requires(), false);
        gatherTerms(rule.ensures(), false);
        filterTerms(rule.body(), true);
        filterTerms(rule.requires(), false);
        filterTerms(rule.ensures(), false);
        return new Rule(
                transform(rule.body(), true),
                transform(rule.requires(), false),
                transform(rule.ensures(), false),
                rule.att());
    }

    private Context resolve(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        gatherTerms(context.body(), true);
        gatherTerms(context.requires(), false);
        filterTerms(context.body(), true);
        filterTerms(context.requires(), false);
        return new Context(
                transform(context.body(), true),
                transform(context.requires(), false),
                context.att());
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

   void gatherTerms(K term, boolean body) {
        AddSortInjections sorts = new AddSortInjections(module);
        new RewriteAwareVisitor(body, new HashSet<>()) {
            @Override
            public void apply(K k) {
                if (isLHS() && !isRHS() && !(k instanceof KVariable)) {
                    cache.put(k, newDotVariable(sorts.sort(k, Sorts.K())));
                }
                super.apply(k);
            }

            @Override
            public void apply(KApply k) {
                if (k.klabel().equals(KLabels.ML_OR)) {
                  return;
                }
                String hook = module.attributesFor().get(k.klabel()).getOrElse(() -> Att.empty()).getOptional("hook").orElse("");
                if (hook.equals("SET.element")
                        || hook.equals("LIST.element")
                        || hook.equals("LIST.concat")
                        || hook.equals("MAP.concat")
                        || hook.equals("SET.concat")) {
                    return;
                }
                if (hook.equals("MAP.element")) {
                    apply(k.items().get(1));
                    return;
                }
                super.apply(k);
            }
        }.apply(term);
    }

    void filterTerms(K term, boolean body) {
        new RewriteAwareVisitor(body, new HashSet<>()) {
            @Override
            public void apply(K k) {
                if (isRHS() && !isLHS() && cache.containsKey(k)) {
                    usedOnRhs.add(k);
                    return;
                }
                super.apply(k);
            }
        }.apply(term);
    }

    K transform(K term, boolean body) {
        AddSortInjections sorts = new AddSortInjections(module);
        return new RewriteAwareTransformer(body) {
            @Override
            public K apply(K k) {
                if (isRHS() && !isLHS()) {
                    if (cache.containsKey(k)) {
                        return cache.get(k);
                    }
                }
                if (isLHS() && !isRHS() && !inBad) {
                    if (usedOnRhs.contains(k)) {
                        return KAs(super.apply(k), cache.get(k), Att.empty().add(Sort.class, cache.get(k).att().get(Sort.class)));
                    }
                }
                return super.apply(k);
            }

            boolean inBad = false;

            @Override
            public K apply(KApply k) {
                boolean stack = inBad;
                if (k.klabel().equals(KLabels.ML_OR)) {
                    inBad = true;
                }
                String hook = module.attributesFor().get(k.klabel()).getOrElse(() -> Att.empty()).getOptional("hook").orElse("");
                if (hook.equals("SET.element")
                        || hook.equals("LIST.element")
                        || hook.equals("LIST.concat")
                        || hook.equals("MAP.concat")
                        || hook.equals("SET.concat")) {
                    inBad = true;
                }
                if (hook.equals("MAP.element")) {
                    inBad = true;
                    K key = apply(k.items().get(0));
                    inBad = stack;
                    K val = apply(k.items().get(1));
                    return KApply(k.klabel(), KList(key, val), k.att());
                }
                K result = super.apply(k);
                inBad = stack;
                return result;
            }

        }.apply(term);
    }

    private int counter = 0;
    KVariable newDotVariable(Sort sort) {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++), Att().add(Sort.class, sort));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

}
