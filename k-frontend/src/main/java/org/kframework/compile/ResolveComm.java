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

public record ResolveComm(KExceptionManager kem) {

  public Module resolve(Module m) {
    // generate a duplicate simplification rule for symbols that are labeled as `comm`
    // remove this attribute from the rules because the Haskell Backend has a different meaning for
    // it
    Set<Sentence> commSimpRules =
        stream(m.localSentences())
            .filter(
                s ->
                    s instanceof Rule
                        && s.att().contains(Att.SIMPLIFICATION())
                        && s.att().contains(Att.COMM()))
            .collect(Collectors.toSet());
    Set<Sentence> commRulesToAdd =
        commSimpRules.stream()
            .flatMap(
                s -> {
                  Rule r = (Rule) s;
                  K newBody = genCommRule(r.body(), m);
                  if (!newBody.equals(r.body()))
                    return Stream.of(
                        Rule.apply(newBody, r.requires(), r.ensures(), r.att().remove(Att.COMM())),
                        Rule.apply(
                            r.body(), r.requires(), r.ensures(), r.att().remove(Att.COMM())));
                  return Stream.of(
                      Rule.apply(r.body(), r.requires(), r.ensures(), r.att().remove(Att.COMM())));
                })
            .collect(Collectors.toSet());
    return Module(
        m.name(),
        m.imports(),
        m.localSentences()
            .$minus$minus(immutable(commSimpRules))
            .$bar(immutable(commRulesToAdd))
            .toSet(),
        m.att());
  }

  public K genCommRule(K body, Module m) {
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
        } else
          kem.addKException(
              new KException(
                  KException.ExceptionType.ERROR,
                  KException.KExceptionGroup.COMPILER,
                  "Used 'comm' attribute on simplification rule but "
                      + k.klabel().name()
                      + " is not comm.",
                  k.att().getOptional(Att.SOURCE(), Source.class).orElse(null),
                  k.att().getOptional(Att.LOCATION(), Location.class).orElse(null)));
        return k;
      }
    }.apply(body);
  }
}
