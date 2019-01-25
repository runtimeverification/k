// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Checks that no two cells with the same name are declared in the configuration.
 */
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

    private Set<Sort> cells = new HashSet<>();

    private void check(Production p) {
        if (p.att().contains(Attribute.CELL_KEY)) {
            for (ProductionItem i : mutable(p.items())) {
                if (i instanceof NonTerminal) {
                    Sort sort = ((NonTerminal) i).sort();
                    if (sort.name().endsWith("Cell")) {
                        if (cells.contains(sort)) {
                            Production cell = new ConfigurationInfoFromModule(module).cellProductionsFor().get(sort).get().head();
                            errors.add(KEMException.compilerError("Cell " + cell.klabel().get() + " found twice in configuration.", p));
                        }
                        cells.add(sort);
                    }
                }
            }
        }
    }
}
