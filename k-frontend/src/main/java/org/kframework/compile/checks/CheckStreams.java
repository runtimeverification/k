// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import static org.kframework.Collections.*;

import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

/** Checks that stream cells have contents of List sort. */
public record CheckStreams(Set<KEMException> errors, Module module) {

  public void check(Sentence s) {
    if (s instanceof Production) {
      check((Production) s);
    }
  }

  private void check(Production p) {
    if (p.att().contains(Att.CELL()) && p.att().contains(Att.STREAM())) {
      ProductionItem i = mutable(p.items()).get(1);
      if (i instanceof NonTerminal) {
        Sort sort = ((NonTerminal) i).sort();
        if (!module.subsorts().lessThanEq(sort, Sorts.List())) {
          errors.add(
              KEMException.compilerError(
                  "Wrong sort in streaming cell. Expected List, but found " + sort.toString() + ".",
                  p));
        }
      } else {
        throw KEMException.internalError("Illegal arguments for stream cell.");
      }
    }
  }
}
