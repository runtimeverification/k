// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KApply;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

public record CheckSmtLemmas(Set<KEMException> errors, Module m) {

  public void check(Sentence sentence) {
    if ((sentence instanceof Rule) && sentence.att().contains(Att.SMT_LEMMA())) {
      check((Rule) sentence);
    }
  }

  private void check(Rule rule) {
    new VisitK() {
      @Override
      public void apply(KApply k) {
        if (m.productionsFor().isDefinedAt(k.klabel())
            && !m.productionsFor()
                .get(k.klabel())
                .get()
                .exists(p -> p.att().contains(Att.SMT_HOOK()) || p.att().contains(Att.SMTLIB()))) {
          errors.add(
              KEMException.compilerError(
                  "Invalid term in smt-lemma detected. All terms in smt-lemma rules require"
                      + " smt-hook or smtlib labels",
                  k));
        }

        k.klist().items().forEach(super::apply);
      }
    }.accept(rule.body());
  }
}
