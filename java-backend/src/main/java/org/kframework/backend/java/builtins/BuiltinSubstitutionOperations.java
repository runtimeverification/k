// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.UserSubstitutionTransformer;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Table of {@code public static} methods on builtin user-level substitution.
 *
 * @author: TraianSF
 */
public class BuiltinSubstitutionOperations {

    public static Term userSubstitution(Term term, Term substitute, Term variable, TermContext context) {
        return KLabelInjection.injectionOf(UserSubstitutionTransformer.userSubstitution(Collections.singletonMap(variable, substitute), term, context), context.global());
    }

    public static Term userSingletonSubstitutionKore(Term term, Term substitute, Term variable, TermContext context) {
        return UserSubstitutionTransformer.userSubstitution(Collections.singletonMap(variable, substitute), term, context);
    }

    public static Term userSubstitutionKore(Term term, BuiltinMap substitution, TermContext context) {
        if (!substitution.isConcreteCollection()) {
            throw new IllegalArgumentException();
        }

        return UserSubstitutionTransformer.userSubstitution(substitution.getEntries(), term, context);
    }

}
