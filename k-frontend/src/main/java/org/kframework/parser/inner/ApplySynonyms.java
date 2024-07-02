// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

import java.util.ArrayList;
import java.util.List;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;

public class ApplySynonyms {

  public Production apply(Module m, Production p) {
    Sort returnSort = m.sortSynonymMap().applyOrElse(p.sort(), s -> p.sort());
    List<ProductionItem> pis = new ArrayList<>();
    for (ProductionItem pi : iterable(p.items())) {
      if (pi instanceof NonTerminal nt) {
        pis.add(NonTerminal(m.sortSynonymMap().applyOrElse(nt.sort(), s -> nt.sort()), nt.name()));
      } else {
        pis.add(pi);
      }
    }
    return Production(p.klabel(), p.params(), returnSort, immutable(pis), p.att());
  }

  public Sentence apply(Module m, Sentence s) {
    if (s instanceof Production) {
      return apply(m, (Production) s);
    } else {
      return s;
    }
  }
}
