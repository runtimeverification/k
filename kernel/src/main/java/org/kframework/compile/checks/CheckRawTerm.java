// Copyright (c) K Team. All Rights Reserved.

package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

public record CheckRawTerm(Set<KEMException> errors) {
  private void check(K k) {
    new VisitK() {
      public void apply(KApply app) {
        if (app.klabel().equals(KLabels.RAW_TERM)) {
          errors.add(
              KEMException.compilerError(
                  "Found usage of "
                      + KLabels.RAW_TERM.name()
                      + "; this production is reserved for K backend usage and"
                      + " cannot appear in user code.",
                  app));
        }

        super.apply(app);
      }
    }.apply(k);
  }

  public void check(Sentence s) {
    if (s instanceof RuleOrClaim r) {
      check(r.body());
      check(r.requires());
      check(r.ensures());
    } else if (s instanceof Context c) {
      check(c.body());
      check(c.requires());
    } else if (s instanceof ContextAlias c) {
      check(c.body());
      check(c.requires());
    }
  }
}
