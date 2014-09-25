// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;


/**
 * Evaluates functions/predicates and collects symbolic constraint generated
 * in the evaluation process.
 */
public class Evaluator extends PrePostTransformer {

    private Evaluator(SymbolicConstraint constraint, TermContext context) {
        super(context);
        this.getPostTransformer().addTransformer(new LocalEvaluator(constraint, context));
    }

    public static Term evaluate(Term term, TermContext context) {
        return Evaluator.evaluate(term, null, context);
    }

    public static Term evaluate(Term term, SymbolicConstraint constraint,
            TermContext context) {
        Evaluator evaluator = new Evaluator(constraint, context);
        return (Term) term.accept(evaluator);
    }
}
