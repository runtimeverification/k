// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.compile.RewriteAwareVisitor;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

/** Check that functions are not used on LHS in places that should be performing matching. */
public record CheckFunctions(Set<KEMException> errors, Module m) {

  public void check(Sentence sentence) {
    if (sentence instanceof Rule rl) {
      checkFuncAtt(rl);
      if (!rl.att().contains(Att.SIMPLIFICATION())) {
        // functions are allowed on the LHS of simplification rules
        check(rl.body());
      }
    } else if (sentence instanceof Context ctx) {
      check(ctx.body());
    } else if (sentence instanceof ContextAlias ctx) {
      check(ctx.body());
    }
  }

  public void check(K body) {
    new RewriteAwareVisitor(true) {
      boolean atTop = true;

      @Override
      public void apply(KApply k) {
        if (k.klabel().name().equals("#withConfig")) {
          super.apply(k);
          return;
        }
        if (k.klabel() instanceof KVariable
            || CheckKLabels.isInternalKLabel(k.klabel().name(), m)
            || !m.attributesFor().contains(k.klabel())) {
          atTop = false;
          super.apply(k);
          return;
        }
        Att attributes = m.attributesFor().apply(k.klabel());
        String hook = attributes.getOptional(Att.HOOK()).orElse("");
        if (attributes.contains(Att.FUNCTION())
            && isLHS()
            && !atTop
            && !(hook.equals("LIST.element")
                || hook.equals("LIST.concat")
                || hook.equals("LIST.unit")
                || hook.equals("SET.element")
                || hook.equals("SET.concat")
                || hook.equals("SET.unit")
                || hook.equals("MAP.element")
                || hook.equals("MAP.concat")
                || hook.equals("MAP.unit")
                || hook.equals("BAG.element")
                || hook.equals("BAG.concat")
                || hook.equals("BAG.unit"))) {
          errors.add(
              KEMException.compilerError(
                  "Illegal function symbol "
                      + k.klabel().name()
                      + " on LHS of rule. Consider adding `simplification` attribute to the rule if"
                      + " this is intended.",
                  k));
        }
        atTop = false;
        if (hook.equals("SET.element")) return;
        if (hook.equals("MAP.element")) {
          apply(k.items().get(1));
          return;
        }
        super.apply(k);
      }
    }.apply(body);
  }

  public void checkFuncAtt(Rule r) {
    new RewriteAwareVisitor(true) {
      @Override
      public void apply(KApply k) {
        if (k.klabel().name().equals("#withConfig")) {
          super.apply(k);
        }
      }
    }.apply(r.body());
  }
}
