// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;

/** Created by dwightguth on 5/28/15. */
public class GenerateSortPredicateSyntax {

  public Module gen(Module mod) {
    Set<Sentence> res = new HashSet<>();
    for (Sort sort : iterable(mod.localSorts())) {
      res.addAll(gen(mod, sort));
    }
    if (!res.isEmpty()) {
      res.add(SyntaxSort(Seq(), Sorts.K()));
    }
    return Module(
        mod.name(), mod.imports(), mod.localSentences().$bar(immutable(res)).toSet(), mod.att());
  }

  public Set<Sentence> gen(Module mod, Sort sort) {
    Production prod =
        Production(
            KLabel("is" + sort.toString()),
            Sorts.Bool(),
            Seq(Terminal("is" + sort), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")),
            Att.empty()
                .add(Att.FUNCTION())
                .add(Att.TOTAL())
                .add(Att.PREDICATE(), Sort.class, sort));
    if (!mod.productions().contains(prod)) return Collections.singleton(prod);
    return Collections.emptySet();
  }
}
