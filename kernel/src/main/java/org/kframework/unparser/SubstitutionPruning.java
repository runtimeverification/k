// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.unparser;

import org.kframework.builtin.KLabels;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import static org.kframework.kore.KORE.KApply;

public class SubstitutionPruning {
    private static final K ML_TRUE = KApply(KLabels.ML_TRUE);

    private Set<K> disjuncts = new HashSet<>();

    /**
     * Takes a pattern assumed to be a disjunction of conjunctions and eliminates all
     * of the conjuncts representing assignments to annonymous variables
     *
     */
    public K pruneSubstitution(K k) {
        leafTransformer(this::isDisjunction,
                leafTransformer(this::isConjunction,
                        this::removeAssignment,
                        this::simplifyAnd)
                        .andThen(this::collectDisjuncts))
                .apply(k);
        Optional<K> reduced = disjuncts.stream().reduce(this::makeDisjunction);
        if (reduced.isPresent()) return reduced.get();
        return KApply(KLabels.ML_FALSE);
    }

    private K makeDisjunction(K k, K k1) {
        return KApply(KLabels.ML_OR, k, k1);
    }

    private K collectDisjuncts(K k) {
        disjuncts.add(k);
        return k;
    }

    private Function<K,K> leafTransformer(Function<KLabel, Boolean> isNode, Function<K, K> transform) {
        return leafTransformer(isNode, transform, x -> x);
    }

    private Function<K,K> leafTransformer(Function<KLabel, Boolean> isNode, Function<K, K> transform, Function<K, K> simplify) {
        TransformK t = new TransformK() {
            @Override
            public K apply(KApply k) {
                if (isNode.apply(k.klabel()))
                    return simplify.apply(super.apply(k));
                return transform.apply(k);
            }

            @Override
            public K apply(KRewrite k) {
                return transform.apply(k);
            }

            @Override
            public K apply(KAs k) {
                return transform.apply(k);
            }

            @Override
            public K apply(KToken k) {
                return transform.apply(k);
            }

            @Override
            public K apply(KVariable k) {
                return transform.apply(k);
            }

            @Override
            public K apply(KSequence k) {
                return transform.apply(k);
            }

            @Override
            public K apply(InjectedKLabel k) {
                return transform.apply(k);
            }
        };
        return k -> t.apply(k);
    }

    private K simplifyAnd(K k) {
        assert k instanceof KApply : "Expecting a ML conjunction";
        KApply and = (KApply) k;
        assert KLabels.ML_AND.equals(and.klabel()) : "Expecting a ML conjunction";
        K first = and.klist().items().get(0);
        K second = and.klist().items().get(1);
        if (ML_TRUE.equals(first)) return second;
        if (ML_TRUE.equals(second)) return first;
        return k;
    }

    private K removeAssignment(K k) {
        if (k instanceof KApply && KLabels.ML_EQUALS.equals(((KApply) k).klabel())) {
            K first = ((KApply) k).klist().items().get(0);
            if (first instanceof KVariable && first.att().contains("anonymous"))
                return ML_TRUE;
        }
        return k;
    }

    private boolean isConjunction(KLabel label) {
        return KLabels.ML_AND.equals(label);
    }

    private boolean isDisjunction(KLabel label) {
        return KLabels.ML_OR.equals(label);
    }
}
