// Copyright (c) 2016-2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import org.kframework.builtin.BooleanUtils;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.Assoc;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 6/1/16.
 */
public class PreprocessKLabelPredicates {

    private final Module m;

    public PreprocessKLabelPredicates(Module m) {
        this.m = m;
    }

    public Sentence convert(Sentence s) {
        if (ExpandMacros.isMacro(s)) {
            return s;
        }
        if (s instanceof Rule) {
            return convert((Rule) s);
        } else {
            return s;
        }
    }

    private Rule convert(Rule rule) {
        Map<KVariable, KApply> predicates = new HashMap<>();
        K requires = rule.requires();
        List<K> clauses = Assoc.flatten(KLabel("_andBool_"), Collections.singletonList(requires), BooleanUtils.TRUE);
        for (K clause : clauses) {
            if (clause instanceof KApply) {
                KApply k = (KApply) clause;
                if (k.klabel() instanceof KVariable) {
                    continue;
                }
                if (m.attributesFor().get(k.klabel()).getOrElse(() -> Att()).contains("klabelPredicate")) {
                    if (k.klist().size() == 1 && k.klist().items().get(0) instanceof InjectedKLabel) {
                        InjectedKLabel injection = (InjectedKLabel) k.klist().items().get(0);
                        if (injection.klabel() instanceof KVariable) {
                            predicates.put((KVariable)injection.klabel(), k);
                        }
                    }
                }
            }
        }
        requires = new TransformK() {
            @Override
            public K apply(KApply k) {
                if (predicates.values().contains(k)) {
                    return BooleanUtils.TRUE;
                }
                return super.apply(k);
            }
        }.apply(requires);
        K body = new TransformK() {
            @Override
            public K apply(KApply k) {
                if (k.klabel() instanceof KVariable && predicates.containsKey(k.klabel())) {
                    return KApply(apply(k.klabel()), k.klist().items().stream().map(this::apply).collect(org.kframework.Collections.toList()), k.att());
                }
                return super.apply(k);
            }

            @Override
            public K apply(InjectedKLabel k) {
                if (k.klabel() instanceof KVariable && predicates.containsKey(k.klabel())) {
                    return InjectedKLabel(apply(k.klabel()), k.att());
                }
                return super.apply(k);
            }

            private KLabel apply(KLabel klabel) {
                KVariable var = (KVariable) klabel;
                return KVariable(var.name(), var.att().add("klabelPredicate", predicates.get(var).klabel().name()));
            }


        }.apply(rule.body());
        return Rule(body, requires, rule.ensures(), rule.att());
    }
}
