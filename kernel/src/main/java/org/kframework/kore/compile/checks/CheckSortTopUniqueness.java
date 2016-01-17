// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.kore.compile.checks;

import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxSort;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import static org.kframework.kore.KORE.Sort;

import java.util.Set;

/**
 * Checks if multiple top sorts KList and Bag are found for
 */
public class CheckSortTopUniqueness {
    private final Set<KEMException> errors;

    private final Module module;

    public CheckSortTopUniqueness(Set<KEMException> errors, Module module) {
        this.errors = errors;
        this.module = module;
    }

    public void check(Sentence s) {
        if (s instanceof Production) {
            check((Production) s);
        } else if (s instanceof SyntaxSort) {
            check((SyntaxSort) s);
        }
    }

    private void check(SyntaxSort p) {
        check(p.sort(), p);
    }

    private void check(Production p) {
        check(p.sort(), p);
    }

    private void check(Sort s, Sentence p) {
        if (!s.equals(Sort("Cell")) &&
                module.subsorts().lessThan(s, Sort("KList")) &&
                module.subsorts().lessThan(s, Sort("Bag"))) {
            errors.add(KEMException.compilerError("Multiple top sorts found for " + s.name() + ": KList and Bag.", p));
        }
    }
}
