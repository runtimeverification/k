// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.Claim;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Check that the `claim` keyword is not used in the definition.
 */
public class CheckClaimInDef {
    private final Set<KEMException> errors;

    public CheckClaimInDef(Set<KEMException> errors) {
        this.errors = errors;
    }

    public void check(Sentence sent) {
        if (sent instanceof Claim)
            errors.add(KEMException.compilerError("Claims are not allowed in the definition.", sent));
    }
}
