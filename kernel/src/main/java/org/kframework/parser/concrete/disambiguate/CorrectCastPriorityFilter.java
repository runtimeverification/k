// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.KSequence;
import org.kframework.kil.Rewrite;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.Cast.CastType;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.PriorityException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CorrectCastPriorityFilter extends ParseForestTransformer {
    private CorrectCastPriorityFilter2 secondFilter;

    public CorrectCastPriorityFilter(Context context) {
        super(CorrectCastPriorityFilter.class.getName(), context);
        secondFilter = new CorrectCastPriorityFilter2(context);
    }

    @Override
    public ASTNode visit(Cast cst, Void _void) throws ParseFailedException {
        // removed variables and allowing only Cast
        // if I find a Cast near a variable, then I remove the cast and translate the sort restrictions to the variable
        // this should be done only if the casting is syntactic, because on semantic cast there should be another branch
        // that has a typed variable.

        Term contents = cst.getContent();
        // it may happen that the variable is wrapped with brackets
        while (contents instanceof Bracket)
            contents = ((Bracket) contents).getContent();
        if (contents instanceof Variable) {
            Variable var = new Variable((Variable) contents);
            if (!var.isUserTyped() && cst.getType() != CastType.OUTER) {
                var.setUserTyped(true);
                var.setSort(cst.getSort());
                var.setSyntactic(cst.getType() != CastType.SEMANTIC);
                var.copyAttributesFrom(cst);
                return var;
            }
        }
        secondFilter.visitNode(cst.getContent());
        return super.visit(cst, _void);
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
            super(CorrectCastPriorityFilter2.class.getName(), context);
        }

        @Override
        public ASTNode visit(KSequence ks, Void _void) throws ParseFailedException {
            assert ks.getContents().size() <= 2;

            String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getSource(), ks.getLocation());
            throw new PriorityException(kex);
        }

        @Override
        public ASTNode visit(Rewrite ks, Void _void) throws ParseFailedException {
            String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getSource(), ks.getLocation());
            throw new PriorityException(kex);
        }

        @Override
        public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
            assert tc.getProduction() != null : this.getClass() + ":" + " production not found." + tc;

            int lastElement = tc.getProduction().getItems().size() - 1;
            if (tc.getProduction().getItems().get(lastElement) instanceof NonTerminal || tc.getProduction().isListDecl()) {
                String msg = "Due to typing errors, Casting is too greedy. Use parentheses to set proper scope.";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, tc.getSource(), tc.getLocation());
                throw new PriorityException(kex);
            }
            return super.visit(tc, _void);
        }

        @Override
        public ASTNode visit(Ambiguity node, Void _void) throws ParseFailedException {
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
