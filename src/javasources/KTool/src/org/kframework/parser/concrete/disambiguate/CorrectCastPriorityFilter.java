// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Cast;
import org.kframework.kil.KSequence;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.Cast.CastType;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CorrectCastPriorityFilter extends ParseForestTransformer {
    private CorrectCastPriorityFilter2 secondFilter;

    public CorrectCastPriorityFilter(Context context) {
        super("Correct Cast priority", context);
        secondFilter = new CorrectCastPriorityFilter2(context);
    }

    @Override
    public ASTNode visit(Cast cst, Void _) throws ParseFailedException {
        // removed variables and allowing only Cast
        // if I find a Cast near a variable, then I remove the cast and translate the sort restrictions to the variable
        // this should be done only if the casting is syntactic, because on semantic cast there should be another branch
        // that has a typed variable.
        if (cst.getContent() instanceof Variable) {
            if (!((Variable) cst.getContent()).isUserTyped() && cst.getType() != CastType.OUTER) {
                Variable var = new Variable((Variable) cst.getContent());
                var.setUserTyped(true);
                var.setSort(cst.getSort());
                var.setSyntactic(cst.getType() != CastType.SEMANTIC);
                return var;
            }
        }
        secondFilter.visitNode(cst.getContent());
        return super.visit(cst, _);
    }

    /**
     * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a Cast
     *
     * if found, throw an exception and until an Ambiguity node catches it
     *
     * @author Radu
     *
     */
    public class CorrectCastPriorityFilter2 extends LocalTransformer {
        public CorrectCastPriorityFilter2(Context context) {
            super("org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter2", context);
        }

        @Override
        public ASTNode visit(KSequence ks, Void _) throws ParseFailedException {
            assert ks.getContents().size() <= 2;

            String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getFilename(), ks.getLocation());
            throw new PriorityException(kex);
        }

        @Override
        public ASTNode visit(Rewrite ks, Void _) throws ParseFailedException {
            String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getFilename(), ks.getLocation());
            throw new PriorityException(kex);
        }

        @Override
        public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
            assert tc.getProduction() != null : this.getClass() + ":" + " cons not found." + tc.getCons();

            int lastElement = tc.getProduction().getItems().size() - 1;
            if (tc.getProduction().getItems().get(lastElement) instanceof Sort || tc.getProduction().isListDecl()) {
                String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getFilename(), tc.getLocation());
                throw new PriorityException(kex);
            }
            return super.visit(tc, _);
        }

        @Override
        public ASTNode visit(Ambiguity node, Void _) throws ParseFailedException {
            ParseFailedException exception = null;
            ArrayList<Term> terms = new ArrayList<Term>();
            for (Term t : node.getContents()) {
                ASTNode result = null;
                try {
                    result = this.visitNode(t);
                    terms.add((Term) result);
                } catch (ParseFailedException e) {
                    exception = e;
                }
            }
            if (terms.isEmpty())
                throw exception;
            if (terms.size() == 1) {
                return terms.get(0);
            }
            node.setContents(terms);
            return node;
        }
    }
}
