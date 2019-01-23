// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.util.HashMap;
import java.util.Map;

/**
 * Renames the anonymous variable to a normal form with index numbers starting from 0.
 * E.g., _1734 + _274 => V0 + V1
 */
class RenameAnonymousVariables {
    Map<Variable, Variable> renames = new HashMap<>();

    int newCount = 0;

    public Variable getRenamedVariable(Variable v) {
        if (v.isAnonymous()) {
            return renames.computeIfAbsent(v, v2 -> new Variable("V" + newCount++, v.sort(), true));
        } else {
            return v;
        }
    }

    public Term apply(Term term) {
        return (Term) term.accept(new CopyOnWriteTransformer() {
            @Override
            public JavaSymbolicObject transform(Variable var) {
                return getRenamedVariable(var);
            }
        });
    }
}
