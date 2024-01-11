// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;

public class CopyDuplicateBytes {
  public static Sentence apply(Sentence s) {
    if (s instanceof Rule r) {
      var rhs = RewriteToTop.toRight(r.body());
      var toWrap = countOccurrences(rhs);

      if (!toWrap.isEmpty()) {
        return Rule(transform(r.body(), toWrap, false), r.requires(), r.ensures(), r.att());
      }
    }

    return s;
  }

  private static K transform(K rule, Set<KVariable> toWrap, boolean underRewrite) {
    return new TransformK() {
      @Override
      public K apply(KApply app) {

        if (Objects.equals(app.klabel().name(), "#SemanticCastToBytes")) {
          if (app.items().size() == 1
              && app.items().get(0) instanceof KVariable var
              && toWrap.contains(var)) {
            if (underRewrite) {
              return wrap(var);
            } else {
              return KRewrite(KApply(KLabel("#SemanticCastToBytes"), var), wrap(var));
            }
          }
        }

        return super.apply(app);
      }

      @Override
      public KRewrite apply(KRewrite rew) {
        return KRewrite(rew.left(), transform(rew.right(), toWrap, true));
      }
    }.apply(rule);
  }

  private static KApply wrap(K k) {
    return KApply(KLabel("copyBytes"), KApply(KLabel("#SemanticCastToBytes"), k));
  }

  private static Set<KVariable> countOccurrences(K rhs) {
    var counts = new HashMap<KVariable, Integer>();

    new VisitK() {
      @Override
      public void apply(KApply app) {
        if (app.klabel().name().equals("#SemanticCastToBytes")) {
          if (app.items().size() == 1 && app.items().get(0) instanceof KVariable var) {
            counts.compute(var, (key, val) -> val == null ? 1 : val + 1);
          }
        }

        super.apply(app);
      }
    }.apply(rhs);

    return counts.entrySet().stream()
        .filter(e -> e.getValue() > 1)
        .map(Map.Entry::getKey)
        .collect(Collectors.toSet());
  }
}
