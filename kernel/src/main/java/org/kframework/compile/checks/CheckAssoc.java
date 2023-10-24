// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Set;

/**
 * Ensure that left, right, and non-assoc are only applied to productions with sorting which permits associativity.
 * That is, if we have `syntax A ::= B "op" C`, then check the following:
 * - if left, then A <= C
 * - if right, then A <= B
 * - if non-assoc, then A <= B and A <= C
 */
public class CheckAssoc {
    private final Set<KEMException> errors;
    private final Module module;

    public CheckAssoc(Set<KEMException> errors, Module module) {
        this.errors = errors;
        this.module = module;
    }

    public void check(Sentence s) {
        if (s instanceof Production p) {
            if (p.arity() != 2) {
                return;
            }
            Sort pSort = p.sort();
            Sort leftSort = p.nonterminals().head().sort();
            Sort rightSort = p.nonterminals().last().sort();
            boolean leqLeft = module.subsorts().lessThanEq(pSort, leftSort);
            boolean leqRight = module.subsorts().lessThanEq(pSort, rightSort);
            if (p.att().contains(Att.LEFT()) && !leqRight) {
                errors.add(KEMException.compilerError(Att.LEFT() +
                        " attribute not permitted on non-associative production.\n" +
                        "Hint: The sub-sorting relation " + pSort + " <= " + rightSort +
                        " does not hold, so the " + Att.LEFT() + " attribute has no effect.", p));
            }
            if (p.att().contains(Att.RIGHT()) && !leqLeft) {
                errors.add(KEMException.compilerError(Att.RIGHT() +
                        " attribute not permitted on non-associative production.\n" +
                        "Hint: The sub-sorting relation " + pSort + " <= " + leftSort +
                        " does not hold, so the " + Att.RIGHT() + " attribute has no effect.", p));
            }
            if (p.att().contains(Att.NON_ASSOC()) && !(leqLeft && leqRight)) {
                errors.add(KEMException.compilerError(Att.NON_ASSOC() +
                        " attribute not permitted on non-associative production.\n" +
                        "Hint: One of the sub-sorting relations " + pSort + " <= " + leftSort + " or " +
                        pSort + " <= " + rightSort + " does not hold, so the " + Att.NON_ASSOC() +
                        " attribute has no effect.", p));
            }
        }
    }
}
