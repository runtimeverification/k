// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Set;

/**
 * Check that rules used in the prover have the `simplification` attribute.
 */
public class CheckProverRules {
    private final Set<KEMException> errors;
    private final KExceptionManager kem;

    public CheckProverRules(Set<KEMException> errors, KExceptionManager kem) {
        this.errors = errors;
        this.kem = kem;
    }

    public void check(Sentence sent) {
        if (sent instanceof Rule && !sent.att().contains("simplification"))
            kem.registerCompilerWarning(KException.ExceptionType.FUTURE_ERROR, errors, "Deprecated: use claim instead of rule to specify proof objectives.", sent);
    }
}
