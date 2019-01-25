// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Checks that stream cells have contents of List sort.
 */
public class CheckStreams {
    private final Set<KEMException> errors;

    private final Module module;

    public CheckStreams(Set<KEMException> errors, Module module) {
        this.errors = errors;
        this.module = module;
    }

    public void check(Sentence s) {
        if (s instanceof Production) {
            check((Production) s);
        }
    }

    private void check(Production p) {
        if (p.att().contains("cell") && p.att().contains("stream")) {
            ProductionItem i = mutable(p.items()).get(1);
            if (i instanceof NonTerminal) {
                Sort sort = ((NonTerminal) i).sort();
                if (!module.subsorts().lessThanEq(sort, Sorts.List())) {
                    errors.add(KEMException.compilerError("Wrong sort in streaming cell. Expected List, but found " + sort.toString() + ".", p));
                }
            } else {
                throw KEMException.internalError("Illegal arguments for stream cell.");
            }
        }
    }
}
