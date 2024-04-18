// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

public record CheckK(Set<KEMException> errors) {

  private void check(K k) {
    new VisitK() {
      @Override
      public void apply(KAs as) {
        boolean error = false;
        if (!(as.alias() instanceof KVariable)) {
          error = true;
          if (as.alias() instanceof KApply app) {
            if (app.klabel().name().startsWith("#SemanticCastTo")
                && app.items().size() == 1
                && app.items().get(0) instanceof KVariable) {
              error = false;
            }
          }
        }
        if (error) {
          errors.add(
              KEMException.compilerError(
                  "Found #as pattern where the right side is not a variable.", as));
        }
        super.apply(as);
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
