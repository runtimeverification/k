// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.compile;

import static org.kframework.kore.KORE.*;

import java.util.*;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Claim;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

/**
 * If a claim doesn't mention the generated counter cell (for resolving fresh variables), then add
 * an implicit `<generatedCounter> _ => ?_ </generatedCounter>` to the claim.
 */
public class AddImplicitCounterCell {

  public AddImplicitCounterCell() {}

  public Sentence apply(Sentence s) {
    if (s instanceof Claim claim) {
      Set<KVariable> freshVars = new HashSet<>();
      VisitK visitor =
          new VisitK() {
            @Override
            public void apply(KVariable var) {
              if (ResolveFreshConstants.isFreshVar(var)) freshVars.add(var);
            }
          };
      visitor.apply(claim.body());
      visitor.apply(claim.requires());
      visitor.apply(claim.ensures());
      // do not add <generatedCounter> if the claim doesn't contain cells or fresh vars
      if (!ConcretizeCells.hasCells(claim.body()) && freshVars.isEmpty()) {
        return s;
      }
      return claim.newInstance(apply(claim.body()), claim.requires(), claim.ensures(), claim.att());
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

  private K apply(K term) {
    List<K> items = IncompleteCellUtils.flattenCells(term);
    if (alreadyHasGeneratedCounter(items)) {
      return term;
    }

    KRewrite rew =
        KRewrite(
            KApply(KLabel("#SemanticCastToInt"), ResolveAnonVar.ANON_VAR),
            KApply(KLabel("#SemanticCastToInt"), ResolveAnonVar.FRESH_ANON_VAR));
    items.add(
        IncompleteCellUtils.make(
            KLabels.GENERATED_COUNTER_CELL, false, Collections.singletonList(rew), false));
    return IncompleteCellUtils.makeBody(items);
  }
}
