// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;
import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

/**
 * Normalizes variable names in terms and sentences according to alpha equivalence. Variables that
 * have previously been normalized are not normalized on succeeding passes, allowing the user to
 * fine-tune the normalization such that arbitrary subterms can share a common prefix.
 */
public class NormalizeVariables {

  private int counter = 0;
  private Map<KVariable, String> vars = new HashMap<>();

  private KVariable normalize(KVariable var) {
    if (var.att().contains(Att.DENORMAL())) return var;
    if (!vars.containsKey(var)) {
      vars.put(var, "_" + counter++);
    }
    return KVariable(vars.get(var), var.att().add(Att.DENORMAL(), var.name()));
  }

  private Map<KVariable, String> inferNormalizationFromTerm(K[] normals) {
    Map<KVariable, String> normalization = new HashMap<>();
    for (K normal : normals) {
      new VisitK() {
        @Override
        public void apply(KVariable k) {
          if (k.att().contains(Att.DENORMAL())) {
            normalization.put(KVariable(k.att().get(Att.DENORMAL())), k.name());
          }
        }
      }.apply(normal);
    }
    return normalization;
  }

  public K normalize(K term, K... normals) {
    resetVars(Stream.concat(Stream.of(term), Arrays.stream(normals)).toArray(K[]::new));
    return transform(term);
  }

  public K transform(K term) {
    return new TransformK() {
      @Override
      public K apply(KVariable k) {
        return normalize(k);
      }
    }.apply(term);
  }

  private void resetVars(K... normals) {
    vars = inferNormalizationFromTerm(normals);
    counter = vars.size();
  }

  public Rule normalize(Rule rule) {
    resetVars(rule.body(), rule.requires(), rule.ensures());
    return Rule(
        transform(rule.body()), transform(rule.requires()), transform(rule.ensures()), rule.att());
  }

  private Context normalize(Context context) {
    resetVars(context.body(), context.requires());
    return new Context(transform(context.body()), transform(context.requires()), context.att());
  }

  public Sentence normalize(Sentence s) {
    if (s instanceof Rule) {
      return normalize((Rule) s);
    } else if (s instanceof Context) {
      return normalize((Context) s);
    } else {
      return s;
    }
  }
}
