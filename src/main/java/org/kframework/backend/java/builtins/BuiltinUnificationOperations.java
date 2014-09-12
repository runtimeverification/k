// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import java.util.Map;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinMgu;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import com.google.common.base.Preconditions;

/**
 * Table of {@code public static} methods on builtin unification.
 *
 * @author: YilongL
 */
public class BuiltinUnificationOperations {

    public static BuiltinMgu updateMgu(BuiltinMgu mgu, Term leftHandSide,
            Term rightHandSide, TermContext context) {
        BuiltinMgu updatedMgu = BuiltinMgu.of(mgu.constraint(), context);
        updatedMgu.constraint().add(leftHandSide, rightHandSide);
        updatedMgu.constraint().simplify();
        // TODO(YilongL): eliminate anony. vars?
        // updatedMgu.constraint().eliminateAnonymousVariables();
        return updatedMgu;
    }

    public static BoolToken isUnificationFailed(BuiltinMgu mgu, TermContext context) {
        mgu.constraint().simplify();
        return mgu.constraint().isFalse() ? BoolToken.TRUE : BoolToken.FALSE;
    }

    public static Term applyMgu(BuiltinMgu mgu, BuiltinMap map,
            TermContext context) {
        Preconditions.checkArgument(!map.hasFrame(), "argument " + map + " has frame");

        BuiltinMap.Builder builder = BuiltinMap.builder();
        Map<Variable, Term> subst = mgu.constraint().substitution();
        for (Map.Entry<Term, Term> entry : map.getEntries().entrySet()) {
            Term value = entry.getValue().substituteWithBinders(subst, context);
            builder.put(entry.getKey(), value);
        }
        return builder.build();
    }

}
