// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;

public class ResolveHeatCoolAttribute {

  private static Rule resolve(Module m, Rule rule) {
    return Rule(rule.body(), transform(m, rule.requires(), rule.att()), rule.ensures(), rule.att());
  }

  private static Context resolve(Module m, Context context) {
    return new Context(
        context.body(), transform(m, context.requires(), context.att()), context.att());
  }

  private static K transform(Module m, K requires, Att att) {
    String sort = att.getOptional(Att.RESULT()).orElse("KResult");
    KLabel lbl = KLabel("is" + sort);
    if (!m.productionsFor().contains(lbl)
        && stream(m.allSorts()).noneMatch(s -> s.toString().equals(sort))) {
      throw KEMException.compilerError(
          "Definition is missing function "
              + lbl.name()
              + " required for strictness. Please either declare sort "
              + sort
              + " or declare 'syntax Bool ::= "
              + lbl.name()
              + "(K) [symbol("
              + lbl.name()
              + "), function]'",
          requires);
    }
    KApply predicate = KApply(lbl, KVariable("HOLE"));
    if (att.contains(Att.HEAT())) {
      return BooleanUtils.and(requires, BooleanUtils.not(predicate));
    }
    if (att.contains(Att.COOL())) {
      return BooleanUtils.and(requires, predicate);
    }
    throw new AssertionError(
        "Called ResolveHeatCoolAttribute::transform on rule without " + "heat or cool attribute");
  }

  public static Sentence resolve(Module m, Sentence s) {
    if (!s.att().contains(Att.HEAT()) && !s.att().contains(Att.COOL())) {
      return s;
    }
    if (s instanceof Rule r) {
      return resolve(m, r);
    } else if (s instanceof Context c) {
      return resolve(m, c);
    } else {
      return s;
    }
  }
}
