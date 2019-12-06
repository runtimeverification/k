// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KAs;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.parser.outer.Outer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.UnaryOperator;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 4/17/15.
 */
public class ResolveSemanticCasts {

    private final boolean skipSortPredicates;
    private Set<KApply> casts = new HashSet<>();
    private Map<KVariable, KVariable> varToTypedVar = new HashMap<>();

    public ResolveSemanticCasts(boolean skipSortPredicates) {

        this.skipSortPredicates = skipSortPredicates;
    }

    void resetCasts() {
        casts.clear();
        varToTypedVar.clear();
    }

    public K resolve(K k) {
        resetCasts();
        gatherCasts(k);
        return transform(k);
    }

    private Rule resolve(Rule rule) {
        resetCasts();
        gatherCasts(rule.body());
        gatherCasts(rule.requires());
        gatherCasts(rule.ensures());
        return new Rule(
                transform(rule.body()),
                addSideCondition(transform(rule.requires()), ExpandMacros.isMacro(rule)),
                transform(rule.ensures()),
                rule.att());
    }

    private Context resolve(Context context) {
        resetCasts();
        gatherCasts(context.body());
        gatherCasts(context.requires());
        return new Context(
                transform(context.body()),
                addSideCondition(transform(context.requires()), false),
                context.att());
    }

    K addSideCondition(K requires, boolean macro) {
        if (skipSortPredicates || macro)
            return requires;
        else {
            Optional<KApply> sideCondition = casts.stream().map(k -> {
                return new TransformK() {
                    @Override
                    public K apply(KVariable k) {
                        if (varToTypedVar.containsKey(k)) {
                            return varToTypedVar.get(k);
                        }
                        return k;
                    }
                }.apply(k);
            }).map(k -> KApply(KLabel("is" + getSortNameOfCast((KApply) k)), transform(k))).reduce(BooleanUtils::and);
            if (!sideCondition.isPresent()) {
                return requires;
            } else if (requires.equals(BooleanUtils.TRUE) && sideCondition.isPresent()) {
                return sideCondition.get();
            } else {
                return BooleanUtils.and(sideCondition.get(), requires);
            }
        }
    }

    public static String getSortNameOfCast(KApply kapp) {
        return kapp.klabel().name().substring("#SemanticCastTo".length());
    }

    void gatherCasts(K term) {
        new VisitK() {
            @Override
            public void apply(KApply v) {
                if (v.klabel().name().startsWith("#SemanticCastTo")) {
                    casts.add(v);
                    K child = v.klist().items().get(0);
                    if (child instanceof KVariable) {
                        KVariable var = (KVariable) child;
                        varToTypedVar.put(var, KVariable(var.name(), var.att().contains(Sort.class) ? var.att() : var.att().add(Sort.class, Outer.parseSort(getSortNameOfCast(v)))));
                    }
                }
                super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformK() {
            private Sort sort;

            @Override
            public K apply(K k) {
                final Sort oldSort = sort;
                K applied;
                if (casts.contains(k)) {
                    KApply kapp = (KApply)k;
                    sort = Outer.parseSort(getSortNameOfCast(kapp));
                    applied = apply(kapp.items().get(0));
                } else {
                    sort = null;
                    applied = super.apply(k);
                }
                if (oldSort != null) {
                  return new AddAtt(a -> a.add(Sort.class, oldSort)).apply(applied);
                }
                if (varToTypedVar.containsKey(applied)) {
                  return varToTypedVar.get(applied);
                }
                return applied;
            }
        }.apply(term);
    }

    public static class AddAtt extends TransformK {
        private final UnaryOperator<Att> f;

        public AddAtt(UnaryOperator<Att> f) {
            this.f = f;
        }

        @Override
        public K apply(KApply kapp) {
            return KApply(kapp.klabel(), kapp.klist(), f.apply(kapp.att()));
        }
        @Override
        public K apply(KRewrite rew) {
            return KRewrite(rew.left(), rew.right(), f.apply(rew.att()));
        }
        @Override
        public K apply(KToken tok) {
            return KToken(tok.s(), tok.sort(), f.apply(tok.att()));
        }
        @Override
        public K apply(KVariable var) {
            return KVariable(var.name(), f.apply(var.att()));
        }
        @Override
        public K apply(KSequence kseq) {
            return KSequence(kseq.items(), f.apply(kseq.att()));
        }
        @Override
        public K apply(InjectedKLabel lbl) {
            return InjectedKLabel(lbl.klabel(), f.apply(lbl.att()));
        }
        @Override
        public K apply(KAs kas) {
            return KAs(kas.pattern(), kas.alias(), f.apply(kas.att()));
        }
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
