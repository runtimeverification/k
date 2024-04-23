// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.kore.KORE.*;

import java.util.HashSet;
import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

public class GuardOrPatterns {

  private final Set<KVariable> vars = new HashSet<>();

  void resetVars() {
    vars.clear();
  }

  private Rule resolve(Module m, Rule rule) {
    resetVars();
    gatherVars(rule.body());
    gatherVars(rule.requires());
    gatherVars(rule.ensures());
    return new Rule(
        transform(rule.body(), m),
        transform(rule.requires(), m),
        transform(rule.ensures(), m),
        rule.att());
  }

  private Context resolve(Module m, Context context) {
    resetVars();
    gatherVars(context.body());
    gatherVars(context.requires());
    return new Context(
        transform(context.body(), m), transform(context.requires(), m), context.att());
  }

  public synchronized Sentence resolve(Module m, Sentence s) {
    if (s instanceof Rule) {
      return resolve(m, (Rule) s);
    } else if (s instanceof Context) {
      return resolve(m, (Context) s);
    } else {
      return s;
    }
  }

  void gatherVars(K term) {
    new VisitK() {
      @Override
      public void apply(KVariable v) {
        vars.add(v);
        super.apply(v);
      }
    }.apply(term);
  }

  K transform(K term, Module m) {
    return new TransformK() {
      @Override
      public K apply(KApply k) {
        if (k.klabel().head().equals(KLabels.ML_OR)) {
          AddSortInjections inj = new AddSortInjections(m);
          return KAs(k, newDotVariable(inj.sort(k, null)));
        }
        return super.apply(k);
      }

      @Override
      public K apply(KAs k) {
        return k;
      }

      @Override
      public K apply(KRewrite k) {
        return k;
      }
    }.apply(term);
  }

  private int counter = 0;

  KVariable newDotVariable(Sort s) {
    if (s == null) {
      s = Sorts.K();
    }
    KVariable newLabel;
    do {
      newLabel =
          KVariable(
              "_Gen" + (counter++),
              Att.empty().add(Att.ANONYMOUS()).add(Att.SORT(), Sort.class, s));
    } while (vars.contains(newLabel));
    vars.add(newLabel);
    return newLabel;
  }
}
