// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;

/**
 * Generates sort predicates from the subsort hierarchy of the module. This module assumes that the
 * backend implements the following rules:
 *
 * <pre>
 *  isSort(#token(Sort, _)) => true
 *  isK(K) => true
 *  isKItem(K1(K2)) => true
 *  isKItem(#token(_, _)) => true
 * </pre>
 *
 * <p>plus one sort membership function for each builtin-hooked sort.
 */
public class GenerateSortPredicateRules {

  public Module gen(Module mod) {
    return Module(
        mod.name(),
        mod.imports(),
        mod.localSentences()
            .$bar(stream(mod.localSorts()).flatMap(this::gen).collect(Collections.toSet()))
            .toSet(),
        mod.att());
  }

  private Stream<? extends Sentence> gen(Sort sort) {
    if (sort.equals(Sorts.K())) {
      return Stream.of(
          Rule(
              KRewrite(KApply(KLabel("is" + sort), KVariable("K")), BooleanUtils.TRUE),
              BooleanUtils.TRUE,
              BooleanUtils.TRUE));
    } else {
      List<Sentence> res = new ArrayList<>();
      res.add(
          Rule(
              KRewrite(
                  KApply(
                      KLabel("is" + sort),
                      KVariable(sort.name(), Att.empty().add(Att.SORT(), Sort.class, sort))),
                  BooleanUtils.TRUE),
              BooleanUtils.TRUE,
              BooleanUtils.TRUE));
      res.add(
          Rule(
              KRewrite(KApply(KLabel("is" + sort), KVariable("K")), BooleanUtils.FALSE),
              BooleanUtils.TRUE,
              BooleanUtils.TRUE,
              Att.empty().add(Att.OWISE())));
      return res.stream();
    }
  }
}
