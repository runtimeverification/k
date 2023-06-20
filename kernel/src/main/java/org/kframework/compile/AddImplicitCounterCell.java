// Copyright (c) K Team. All Rights Reserved.

package org.kframework.compile;

import org.kframework.builtin.KLabels;
import org.kframework.definition.Claim;
import org.kframework.definition.Sentence;
import org.kframework.definition.Module;
import org.kframework.kore.*;

import java.util.*;

import static org.kframework.kore.KORE.*;

/**
 * If a claim doesn't mention the generated counter cell (for resolving fresh variables),
 * then add an implicit `<generatedCounter> _ => ?_ </generatedCounter>` to the claim.
 */
public class AddImplicitCounterCell {

    public AddImplicitCounterCell() {}

    public Sentence apply(Module m, Sentence s) {
        if(s instanceof Claim) {
            Claim claim = (Claim) s;
            return claim.newInstance(apply(claim.body(), m), claim.requires(), claim.ensures(), claim.att());
        }
        return s;
    }

    // We shouldn't add the implicit cell to the claim if the user has already written
    // it explicitly.
    private boolean alreadyHasGeneratedCounter(List<K> items) {
        return items.stream()
                .filter(cell -> cell instanceof KApply)
                .anyMatch(cell -> ((KApply) cell).klabel().equals(KLabels.GENERATED_COUNTER_CELL));
    }

    private K apply(K term, Module m) {
        List<K> items = IncompleteCellUtils.flattenCells(term);
        if(alreadyHasGeneratedCounter(items)) {
            return term;
        }

        KRewrite rew = KRewrite(
                KApply(KLabel("#SemanticCastToInt"), ResolveAnonVar.ANON_VAR),
                KApply(KLabel("#SemanticCastToInt"), ResolveAnonVar.FRESH_ANON_VAR));
        items.add(IncompleteCellUtils.make(
                KLabels.GENERATED_COUNTER_CELL, false, Collections.singletonList(rew), false));
        return IncompleteCellUtils.makeBody(items);
    }

}
