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
import org.kframework.utils.errorsystem.KEMException;

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
    if (!(pushed instanceof KApply app)) {
      throw KEMException.internalError("pushUp invariant violated");
    }

    return app.items().stream()
        .map(
            lhs ->
                (RuleOrClaim)
                    new Rule(KRewrite(lhs, right), rule.requires(), rule.ensures(), rule.att()))
        .collect(Collectors.toSet());
  }

  /**
   * Check whether a term is an {@code #Or} application.
   *
   * <p>Note that because this pass is run after sort parameters have been instantiated, the klabel
   * of {@code #Or} terms will actually be {@code #Or{Sort}}, and so we need to check prefixes
   * rather than strict equality of labels here.
   *
   * @param k The term to check.
   * @return {@code true} if {@code k} is a top-level application whose klabel begins with {@code
   *     #Or}.
   */
  private static boolean isMLOr(K k) {
    return k instanceof KApply app && app.klabel().name().startsWith(KLabels.ML_OR.name());
  }

  /**
   * Take the cross product over all {@code #Or} argument lists in {@code args} to produce a nested
   * list of or-free argument lists.
   *
   * <p>For example:
   *
   * <pre>
   *     expand [a, #Or(b, c), #Or(d, e)] => [ [a, b, d], [a, c, d], [a, b, e], [a, c, e] ]
   * </pre>
   *
   * <p>This expansion process is generic across different types of K term; the resulting nested
   * list can then be reassembled into applications, sequences etc. as appropriate by the caller.
   *
   * @param args A list of K terms, potentially containing {@code #Or} terms.
   * @return A nested list of or-free K term lists, each of which represents a concrete selection of
   *     every {@code #Or} in {@code args}.
   */
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

        if (!(next.get(idx) instanceof KApply app)) {
          throw KEMException.internalError("inconsistent isMLOr result");
        }

        for (var arg : app.items()) {
          var result = new ArrayList<>(preArgs);
          result.add(arg);
          result.addAll(postArgs);
          queue.add(result);
        }
      }
    }

    return results;
  }

  /**
   * Push any {@code #Or} terms that are direct children of {@code k} to the top, expanding as
   * necessary.
   *
   * <p>Even if there are no disjunctions inside {@code k}, the top level term returned here will be
   * an application of {@code #Or} (with a single argument). The rule-expansion entrypoint to the
   * overall pass will resolve these cases. For example:
   *
   * <pre>
   *     pushUp foo(a #Or b)    => foo(a) #Or foo(b)
   *     pushUp (a #Or b) ~> c  => (a ~> c) #Or (b ~> c)
   *     pushUp a               => `#Or`(a)
   * </pre>
   *
   * @param k The term to push up and expand.
   * @return An application of {@code #Or} that is equivalent to {@code k}, and the children of
   *     which are all or-free.
   */
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

  /**
   * Recursively flatten the arguments of nested {@code #Or} terms.
   *
   * <p>For example:
   *
   * <pre>
   *     flattenOr [a, #Or(b, c), d] => [a, b, c, d]
   * </pre>
   *
   * @param args The arguments of a {@code #Or} term to flatten.
   * @return The same argument list, with all instances of {@code #Or} terms flattened.
   */
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

  /**
   * Specialization of {@link #pushUp(K)} for applications.
   *
   * <p>If {@code app} is an {@code #Or} pattern, we enforce the push-up invariant by simply
   * flattening its arguments such that no children are themselves {@code #Or} patterns.
   *
   * <p>Otherwise, we push {@code #Or} to the top of each argument, then expand the resulting list
   * of arguments. For each expanded argument list, we then wrap it in {@code app}'s top-level
   * constructor, and take the disjunction over that set of terms.
   *
   * @param app The application to push up and expand.
   * @return An application of {@code #Or} equivalent to {@code app}, where each disjunct case is
   *     or-free.
   */
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

  /**
   * Specialization of {@link #pushUp(K)} for applications.
   *
   * <p>We push {@code #Or} to the top of each element of the sequence, then expand the resulting
   * list of arguments. For each expanded argument list, we then turn it back into a K sequence, and
   * take the disjunction over that set of terms.
   *
   * @param seq The sequence to push up and expand.
   * @return An application of {@code #Or} equivalent to {@code seq}, where each disjunct case is
   *     or-free.
   */
  private static K pushUp(KSequence seq) {
    var pushed = seq.items().stream().map(EliminateOrPatterns::pushUp).toList();
    var expanded = expand(pushed);

    var orArgs = expanded.stream().map(args -> (K) KSequence(args)).toList();

    return KApply(KLabels.ML_OR, KList(orArgs));
  }

  /**
   * Specialization of {@link #pushUp(K)} for as-patterns.
   *
   * <p>We push {@code #Or} to the top of the bound pattern, then expand the resulting list of
   * arguments. For each expanded argument list, we then turn it back into a binding to the same
   * alias, and take the disjunction over that set of terms.
   *
   * @param as The as-pattern to push up and expand.
   * @return An application of {@code #Or} equivalent to {@code as}, where each disjunct case is
   *     or-free.
   */
  private static K pushUp(KAs as) {
    var pushed = Collections.singletonList(pushUp(as.pattern()));
    var expanded = expand(pushed);

    var orArgs = expanded.stream().map(args -> (K) KAs(args.get(0), as.alias(), as.att())).toList();
    return KApply(KLabels.ML_OR, KList(orArgs));
  }
}
