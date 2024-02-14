// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Production;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;

public record CheckDeprecated(Set<KEMException> errors, KExceptionManager kem) {
  public void check(Production p, K term) {
    if (p.att().contains(Att.DEPRECATED())) {
      kem.registerCompilerWarning(
          KException.ExceptionType.DEPRECATED_SYMBOL,
          errors,
          "Use of deprecated production found; this syntax may be removed in the future.",
          term);
    }
  }

  public void check(K k) {
    new VisitK() {
      @Override
      public void apply(K term) {
        term.att().getOptional(Att.PRODUCTION(), Production.class).ifPresent(p -> check(p, term));
        super.apply(term);
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
