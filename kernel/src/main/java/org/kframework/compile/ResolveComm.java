// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.immutable;
import static org.kframework.Collections.stream;
import static org.kframework.definition.Constructors.Module;

import com.google.common.collect.Lists;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * Generate reordered cases for simplification rules that have the `comm` attribute.
 *
 * <p>For example, given the simplification:
 *
 * <pre>
 *         rule { 1 +Int 2 #Equals 3 } => #Top [comm, simplification]
 * </pre>
 *
 * we would generate a second simplification rule by swapping the sides of the top-level `#Equals`
 * symbol:
 *
 * <pre>
 *         rule { 3 #Equals 1 +Int 2 } => #Top
 * </pre>
 *
 * Note that the pass also strips the `comm` attribute from both cases of the simplification. This
 * is because of an outstanding issue where the attribute has two overloaded meanings, depending on
 * where it is used:
 *
 * <ul>
 *   <li><a href="https://github.com/runtimeverification/k/issues/2774">K issue #2774</a>
 * </ul>
 *
 * Preconditions:
 *
 * <ul>
 *   <li>None
 * </ul>
 *
 * Postconditions:
 *
 * <ul>
 *   <li>There are no user-supplied simplification rules with the `comm` attribute.
 * </ul>
 *
 * @param kem
 */
public record ResolveComm(KExceptionManager kem) {

  public Module resolve(Module m) {
    Set<Sentence> commSimpRules =
        stream(m.localSentences())
            .filter(ResolveComm::isCommutativeSimplification)
            .collect(Collectors.toSet());

    Set<Sentence> commRulesToAdd =
        commSimpRules.stream().flatMap(s -> generateRulesFrom(s, m)).collect(Collectors.toSet());

    return Module(
        m.name(),
        m.imports(),
        m.localSentences()
            .$minus$minus(immutable(commSimpRules))
            .$bar(immutable(commRulesToAdd))
            .seq(),
        m.att());
  }

  private static boolean isCommutativeSimplification(Sentence s) {
    return s instanceof Rule
        && s.att().contains(Att.SIMPLIFICATION())
        && s.att().contains(Att.COMM());
  }

  /*
   * If permuting the top-level arguments of this rule produces a new, distinct rule,
   * return both those rules. Otherwise, return only the original rule (though in both cases,
   * the `comm` attribute is stripped).
   */
  private Stream<Rule> generateRulesFrom(Sentence rule, Module m) {
    if (!(rule instanceof Rule r)) {
      return Stream.empty();
    }

    K newBody = genCommRule(r.body(), m);

    if (newBody.equals(r.body())) {
      return Stream.of(Rule.apply(r.body(), r.requires(), r.ensures(), r.att().remove(Att.COMM())));
    }

    return Stream.of(
        Rule.apply(newBody, r.requires(), r.ensures(), r.att().remove(Att.COMM())),
        Rule.apply(r.body(), r.requires(), r.ensures(), r.att().remove(Att.COMM())));
  }

  /*
   * Create a new rule by permuting the arguments of the top-level application on the left-hand
   * side of a rule. If the symbol at the top of the LHS does not have the `comm` attribute itself,
   * then raise a compiler error. In practice, this means a restriction on the LHS to commutative
   * ML symbols like `#Equals`, `#And` etc.
   */
  private K genCommRule(K body, Module m) {
    return new RewriteAwareTransformer(true) {
      @Override
      public K apply(KApply k) {
        if (k.klabel().name().equals("#withConfig")) {
          return super.apply(k);
        }

        if ((isRHS() && !isLHS())
            || k.klabel() instanceof KVariable
            || !m.attributesFor().contains(k.klabel())) {
          return k;
        }

        Att attributes = m.attributesFor().apply(k.klabel());
        if (attributes.contains(Att.COMM())) {
          return KORE.KApply(
              k.klabel(),
              KORE.KList(Lists.newArrayList(k.klist().items().get(1), k.klist().items().get(0))),
              k.att());
        } else {
          kem.addKException(
              new KException(
                  KException.ExceptionType.ERROR,
                  KException.KExceptionGroup.COMPILER,
                  "Used 'comm' attribute on simplification rule but "
                      + k.klabel().name()
                      + " is not comm.",
                  k.att().getOptional(Source.class).orElse(null),
                  k.att().getOptional(Location.class).orElse(null)));
        }

        return k;
      }
    }.apply(body);
  }
}
