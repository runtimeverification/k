// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 4/17/15.
 */
public class ResolveSemanticCasts {

    private Set<KApply> casts = new HashSet<>();
    private Map<KVariable, KVariable> varSorts = new HashMap<>();

    void resetCasts() {
        casts.clear();
        varSorts.clear();
    }

    private Rule resolve(Rule rule) {
        resetCasts();
        gatherCasts(rule.body());
        gatherCasts(rule.requires());
        gatherCasts(rule.ensures());
        return new Rule(
                transform(rule.body()),
                addSideCondition(transform(rule.requires())),
                transform(rule.ensures()),
                rule.att());
    }

    private Context resolve(Context context) {
        resetCasts();
        gatherCasts(context.body());
        gatherCasts(context.requires());
        return new Context(
                transform(context.body()),
                addSideCondition(transform(context.requires())),
                context.att());
    }

    K addSideCondition(K requires) {
        return casts.stream().map(kapp -> (K) KApply(KLabel("is" + getSortNameOfCast(kapp)), KList(kapp.klist().items().stream().map(varSorts::get).collect(Collectors.toList())), kapp.att()))
                .reduce(requires, BooleanUtils::and);
    }

    private String getSortNameOfCast(KApply kapp) {
        return kapp.klabel().name().substring("#SemanticCastTo".length());
    }

    void gatherCasts(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KApply v) {
                if (v.klabel().name().startsWith("#SemanticCastTo")) {
                    casts.add(v);
                    K child = v.klist().items().get(0);
                    if (child instanceof KVariable) {
                        KVariable var = (KVariable) child;
                        varSorts.put(var, KVariable(var.name(), var.att().add("sort", getSortNameOfCast(v))));
                    }
                }
                return super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                if (casts.contains(k)) {
                    return super.apply(k.klist().items().get(0));
                }
                return super.apply(k);
            }

            @Override
            public K apply(KVariable k) {
                if (varSorts.containsKey(k)) {
                    return varSorts.get(k);
                }
                return super.apply(k);
            }
        }.apply(term);
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
}
