// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.kore.KORE.*;

import java.util.HashMap;
import java.util.Map;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.kore.K;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.utils.errorsystem.KEMException;

public class ResolveFreshConfigConstants {
  private int currentFresh = 0;
  private final Map<KVariable, Integer> freshMap = new HashMap<>();

  /**
   * Replaces fresh variables in the RHS of cell initializer rules with a fresh constant.
   *
   * <p>There is a question of whether fresh config variables with the same name but in different
   * modules should generate different constants. For the sake of simplicity, and to allow the use
   * case, no distinction is made between different modules.
   *
   * @param r The rule that initializes the cell
   * @param body The KRewrite for the rule
   * @return The body is returned with any fresh variables in the RHS replaced with a fresh constant
   */
  private K transform(RuleOrClaim r, K body) {
    if (!(r instanceof Rule rule)) {
      return body;
    }

    if (!rule.att().contains(Att.INITIALIZER())) {
      return body;
    }

    return new TransformK() {
      @Override
      public K apply(KVariable k) {
        if (k.name().startsWith("!")) {
          if (!k.att().get(Att.SORT(), Sort.class).equals(Sorts.Int())) {
            throw KEMException.compilerError(
                "Can't resolve fresh configuration variable not of sort Int", k);
          }
          if (k.att().contains(Att.ANONYMOUS())) {
            return KToken(Integer.toString(currentFresh++), Sorts.Int());
          }
          if (!freshMap.containsKey(k)) {
            freshMap.put(k, currentFresh++);
          }
          return KToken(Integer.toString(freshMap.get(k)), Sorts.Int());
        }
        return k;
      }

      @Override
      public K apply(KRewrite k) {
        return KRewrite(k.left(), apply(k.right()), k.att());
      }
    }.apply(body);
  }

  public Module resolve(Module m) {
    return ModuleTransformer.fromRuleBodyTransformerWithRule(
            (r, body) -> transform(r, body), "Resolve fresh variables in cell initializers")
        .apply(m);
  }

  /**
   * Gets the number of fresh constants that were generated.
   *
   * <p>This is used in the next stage of the pipeline where the generatedCounter cell is added to
   * the configuration. The initializer rule for the generatedCounter will use this value so any
   * fresh values during execution do not conflict with the values in the initial configuration.
   *
   * @return What the generatedCounter should be initialized to.
   */
  public int getCurrentFresh() {
    return currentFresh;
  }
}
