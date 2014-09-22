// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;


/**
 * Expands map patterns according to their definitions.
 */
public class PatternExpander extends PrePostTransformer {

    private PatternExpander(SymbolicConstraint constraint, boolean narrow, TermContext context) {
        super(context);
        this.getPostTransformer().addTransformer(new LocalPatternExpander(constraint, narrow, context));
    }

    public static Term expand(Term term, SymbolicConstraint constraint, boolean narrow, TermContext context) {
        return (Term) term.accept(new PatternExpander(constraint, narrow, context));
    }

    private static class LocalPatternExpander extends LocalTransformer {

        /**
        * The symbolic constraint of the {@code ConstrainedTerm} which contains the
        * terms to be evaluated by this evaluator.
        */
        private final SymbolicConstraint constraint;
        private final boolean narrow;

        public LocalPatternExpander(SymbolicConstraint constraint, boolean narrow, TermContext context) {
            super(context);
            this.constraint = constraint;
            this.narrow = narrow;
        }

        public ASTNode transform(KItem kItem) {
            return kItem.expandPattern(constraint, narrow, context);
        }

    }
}
