// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.parser.outer.Outer;

import java.util.Set;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveHeatCoolAttribute {

    private Set<String> transitions;

    public ResolveHeatCoolAttribute(Set<String> transitions) {
        this.transitions = transitions;
    }

    private Rule resolve(Rule rule) {
        return Rule(
                transformBody(rule.body(), rule.att()),
                transform(rule.requires(), rule.att()),
                rule.ensures(),
                rule.att());
    }

    private Context resolve(Context context) {
        return new Context(
                transformBody(context.body(), context.att()),
                transform(context.requires(), context.att()),
                context.att());
    }

            private K transformBody(K body, Att att) {
                if (att.contains("cool")) {
                    return new TransformK() {
                        public K apply(KVariable var) {
                            if (var.name(). equals("HOLE") && transitions.stream().noneMatch(att::contains)) {
                                return KVariable(var.name(), var.att().add(Sort.class, Outer.parseSort(att.getOptional("result").orElse("KResult"))));
                            }
                            return super.apply(var);
                        }
                    }.apply(body);
                }
                return body;
            }

    private K transform(K requires, Att att) {
        String sort = att.<String>getOptional("result").orElse("KResult");
        KApply predicate = KApply(KLabel("is" + sort), KVariable("HOLE"));
        if (att.contains("heat")) {
            return BooleanUtils.and(requires, BooleanUtils.not(predicate));
        } else if (att.contains("cool")) {
            if (transitions.stream().anyMatch(att::contains)) {
                // if the cooling rule is a super strict, then tag the isKResult predicate and drop it during search
                predicate = KApply(predicate.klabel(), predicate.klist(), predicate.att().add(Att.transition()));
            }
            return BooleanUtils.and(requires, predicate);
        }
        throw new AssertionError("unreachable");
    }

    public Sentence resolve(Sentence s) {
        if (!s.att().contains("heat") && !s.att().contains("cool")) {
            return s;
        }
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else {
            return s;
        }
    }
}
