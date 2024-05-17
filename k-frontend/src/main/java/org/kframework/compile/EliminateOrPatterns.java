// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.kore.KORE.*;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KSequence;

public record EliminateOrPatterns() {
  /**
   * Expand all {@code #Or} patterns in rules to produce an equivalent set of rules, none of which
   * contain any {@code #Or} patterns.
   *
   * <p>This transformation is necessary because backend support for {@code #Or} is inconsistent;
   * the LLVM backend can pattern-match on {@code #Or} patterns on the left-hand side of rules, but
   * the Haskell backend cannot internalize such patterns.
   *
   * <p>For example, the rule:
   *
   * <pre>
   *     rule foo(a #Or b) => c
   * </pre>
   *
   * <p>Will expand to two rules:
   *
   * <pre>
   *     rule foo(a) => c
   *     rule foo(b) => c
   * </pre>
   *
   * <p>Note that rules are implicitly transformed into top-level rewrites by this pass; extracting
   * the correct disjunct rules is severely complicated if we don't put the rules in this form. This
   * pass must therefore be run right at the end of compilation before generating KORE.
   *
   * @param rc A rule possibly containing {@code #Or} patterns to be expanded.
   * @return A set of disjunct rules that model the behaviour of {@code rc} when combined.
   */
  public static Set<RuleOrClaim> expand(RuleOrClaim rc) {
    if (!(rc instanceof Rule rule)) {
      return Collections.singleton(rc);
    }

    K left = RewriteToTop.toLeft(rule.body());
    K right = RewriteToTop.toRight(rule.body());

    var pushed = pushUp(left);
    assert isMLOr(pushed);

    return ((KApply) pushed)
        .items().stream()
            .map(
                lhs ->
                    (RuleOrClaim)
                        new Rule(KRewrite(lhs, right), rule.requires(), rule.ensures(), rule.att()))
            .collect(Collectors.toSet());
  }

  private static boolean isMLOr(K k) {
    return k instanceof KApply app && app.klabel().name().startsWith(KLabels.ML_OR.name());
  }

  private static List<List<K>> expand(List<K> args) {
    var queue = new ArrayDeque<List<K>>();
    var results = new ArrayList<List<K>>();

    queue.add(args);

    while (!queue.isEmpty()) {
      var next = queue.pop();
      var orIdx = IntStream.range(0, next.size()).filter(i -> isMLOr(next.get(i))).findFirst();

      if (orIdx.isEmpty()) {
        results.add(next);
      } else {
        var idx = orIdx.getAsInt();

        var preArgs = next.subList(0, idx);
        var postArgs = next.subList(idx + 1, next.size());

        var app = (KApply) next.get(idx);
        for (var arg : app.items()) {
          var result = new ArrayList<K>(preArgs);
          result.add(arg);
          result.addAll(postArgs);
          queue.add(result);
        }
      }
    }

    return results;
  }

  private static K pushUp(K k) {
    if (k instanceof KApply app) {
      return pushUp(app);
    }

    if (k instanceof KSequence seq) {
      return pushUp(seq);
    }

    if (k instanceof KAs as) {
      return pushUp(as);
    }

    return KApply(KLabels.ML_OR, KList(k));
  }

  private static List<K> flattenOr(List<K> args) {
    var result = new ArrayList<K>();

    for (var a : args) {
      if (a instanceof KApply app && isMLOr(app)) {
        result.addAll(flattenOr(app.items()));
      } else {
        result.add(a);
      }
    }

    return result;
  }

  private static K pushUp(KApply app) {
    if (isMLOr(app)) {
      return KApply(KLabels.ML_OR, KList(flattenOr(app.items())));
    }

    var pushed = app.items().stream().map(EliminateOrPatterns::pushUp).toList();
    var expanded = expand(pushed);

    var orArgs =
        expanded.stream().map(args -> (K) KApply(app.klabel(), KList(args), app.att())).toList();
    return KApply(KLabels.ML_OR, KList(orArgs));
  }

  private static K pushUp(KSequence seq) {
    var pushed = seq.items().stream().map(EliminateOrPatterns::pushUp).toList();
    var expanded = expand(pushed);

    var orArgs = expanded.stream().map(args -> (K) KSequence(args)).toList();

    return KApply(KLabels.ML_OR, KList(orArgs));
  }

  private static K pushUp(KAs as) {
    var pushed = Collections.singletonList(pushUp(as.pattern()));
    var expanded = expand(pushed);

    var orArgs = expanded.stream().map(args -> (K) KAs(args.get(0), as.alias(), as.att())).toList();
    return KApply(KLabels.ML_OR, KList(orArgs));
  }
}
