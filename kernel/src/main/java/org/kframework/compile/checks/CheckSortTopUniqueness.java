// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.definition.SyntaxSort;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Check that every sort has an unique top (super) sort.
 * For example, the following is not allowed, since A has multiple top sorts, KList and Bag:
 *   syntax A
 *   syntax KList ::= A
 *   syntax Bag ::= A
 */
public class CheckSortTopUniqueness {
    private final Set<KEMException> errors;

    private final Module module;

    /**
     * Check that the given module has no sort that has multiple top sorts.
     * @param errors to be updated when violations occur. Multiple violations will be accumulated in `errors`.
     * @param module to be checked.
     */
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
        if (!s.equals(Sorts.Cell()) &&
                module.subsorts().lessThan(s, Sorts.KList()) &&
                module.subsorts().lessThan(s, Sorts.Bag())) {
            errors.add(KEMException.compilerError("Multiple top sorts found for " + s.toString() + ": KList and Bag.", p));
        }
    }
}
