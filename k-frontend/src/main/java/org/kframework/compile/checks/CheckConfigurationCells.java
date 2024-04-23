// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile.checks;

import static org.kframework.Collections.*;

import java.util.HashSet;
import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

/** Checks that no two cells with the same name are declared in the configuration. */
public class CheckConfigurationCells {
  private final Set<KEMException> errors;

  private final Module module;

  public CheckConfigurationCells(Set<KEMException> errors, Module module) {
    this.errors = errors;
    this.module = module;
  }

  public void check(Sentence s) {
    if (s instanceof Production) {
      check((Production) s);
    }
  }

  private final Set<Sort> cells = new HashSet<>();

  private void check(Production p) {
    if (p.att().contains(Att.CELL())) {
      for (ProductionItem i : mutable(p.items())) {
        if (i instanceof NonTerminal) {
          Sort sort = ((NonTerminal) i).sort();
          if (sort.name().endsWith("Cell")) {
            if (cells.contains(sort)) {
              Production cell =
                  new ConfigurationInfoFromModule(module)
                      .cellProductionsFor()
                      .get(sort)
                      .get()
                      .head();
              errors.add(
                  KEMException.compilerError(
                      "Cell " + cell.klabel().get() + " found twice in configuration.", p));
            }
            cells.add(sort);
          }
        }
      }
      if (p.att().getOptional(Att.MULTIPLICITY()).orElse("").equals("*")
          && p.att().getOptional(Att.TYPE()).orElse("Bag").equals("Bag")) {
        errors.add(
            KEMException.compilerError(
                "Cell bags are only supported on the Java backend. If you want this feature,"
                    + " comment on https://github.com/runtimeverification/k/issues/1419 . As a"
                    + " workaround, you can add the attribute type=\"Set\" and add a unique"
                    + " identifier to each element in the set.",
                p));
      }
    }
  }
}
