// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import java.util.HashSet;
import java.util.List;
import javax.annotation.Nullable;
import org.kframework.attributes.Att;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Rule;
import org.kframework.utils.errorsystem.KEMException;

public class MarkExtraConcreteRules {

  /** Mark with [concrete] rules with labels enumerated in `--concrete-rules`. */
  public static Definition mark(Definition def, @Nullable List<String> extraConcreteRuleLabels) {
    if (extraConcreteRuleLabels == null) {
      return def;
    }
    HashSet<String> concreteLabelsSet = new HashSet<>(extraConcreteRuleLabels);
    Definition result =
        DefinitionTransformer.fromSentenceTransformer(
                (mod, s) -> {
                  if (s instanceof Rule r) {
                    String label = r.att().getOption(Att.LABEL()).getOrElse(() -> null);
                    if (label != null && concreteLabelsSet.contains(label)) {
                      // rule labels must be unique, so it's safe to remove from the set as we
                      // iterate
                      concreteLabelsSet.remove(label);
                      return Rule.apply(
                          r.body(), r.requires(), r.ensures(), r.att().add(Att.CONCRETE()));
                    }
                  }
                  return s;
                },
                "mark extra concrete rules")
            .apply(def);
    if (!concreteLabelsSet.isEmpty()) {
      throw KEMException.criticalError("Unused concrete rule labels: " + concreteLabelsSet);
    }
    return result;
  }
}
