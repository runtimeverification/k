// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;


/**
 * Evaluates pending functions inside a term.
 */
public class Evaluator extends CopyOnWriteTransformer {

    public Evaluator(TermContext context) {
        super(context);
    }

    public static Term evaluate(Term term, TermContext context) {
        Evaluator evaluator = new Evaluator(context);
        return (Term) term.accept(evaluator);
    }

    @Override
    public JavaSymbolicObject transform(KItem kItem) {
        if (kItem.isEvaluatedRecursively()) {
            return kItem;
        }
        Term result = ((KItem) super.transform(kItem)).resolveFunctionAndAnywhere(context);
        if (result instanceof KItem && result.isGround()) {
            ((KItem) result).setEvaluatedRecursively(true);
        }

        return result;
    }

    @Override
    public JavaSymbolicObject<Term> transform(KItemProjection kItemProjection) {
        return ((KItemProjection) super.transform(kItemProjection)).evaluateProjection();
    }

}
