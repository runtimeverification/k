// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.kore.compile.checks;

import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.utils.errorsystem.KEMException;

import static org.kframework.Collections.*;

import java.util.HashSet;
import java.util.Set;

/**
 * Checks that no two cells with the same name are declared in the configuration.
 */
public class CheckConfigurationCells {
    private final Set<KEMException> errors;

    public CheckConfigurationCells(Set<KEMException> errors) {
        this.errors = errors;
    }

    public void check(Sentence s) {
        if (s instanceof Production) {
            check((Production) s);
        }
    }

    private Set<String> cells = new HashSet<String>();

    private void check(Production p) {
        if (p.att().contains(Attribute.CELL_KEY)) {
            for (ProductionItem i : mutable(p.items())) {
                if (i instanceof NonTerminal) {
                    String sort = ((NonTerminal) i).sort().name();
                    if (sort.endsWith("Cell")) {
                        if (cells.contains(sort)) {
                            errors.add(KEMException.compilerError("Cell " + sort + " found twice in configuration.", p));
                        }
                        cells.add(sort);
                    }
                }
            }
        }
    }
}
