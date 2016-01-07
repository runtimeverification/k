// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import scala.collection.mutable.HashMap;
import scala.collection.mutable.Map;
import static scala.compat.java8.JFunction.*;

/**
 * Renames the anonymous variable to a normal form with index numbers starting from 0.
 * E.g., _1734 + _274 => V0 + V1
 */
class RenameAnonymousVariables {
    @SuppressWarnings("unchecked")
    Map<Variable, Variable> renames = new HashMap<>();

    int newCount = 0;

    public Variable getRenamedVariable(Variable v) {
        if (v.isAnonymous()) {
            return renames.getOrElseUpdate(v, func(() -> new Variable("V" + newCount++, v.sort())));
        } else {
            return v;
        }
    }

    public Term apply(Term term) {
        return (Term) term.accept(new CopyOnWriteTransformer() {
            @Override
            public ASTNode transform(Variable var) {
                return getRenamedVariable(var);
            }
        });
    }
}
