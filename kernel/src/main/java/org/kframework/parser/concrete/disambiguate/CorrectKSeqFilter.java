// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.KSequence;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.PriorityException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CorrectKSeqFilter extends ParseForestTransformer {
    private CorrectKSeqFilter2 secondFilter;

    public CorrectKSeqFilter(Context context) {
        super("Correct K sequences", context);
        secondFilter = new CorrectKSeqFilter2(context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _void) throws ParseFailedException {
        List<Term> children = new ArrayList<Term>();
        for (Term t : amb.getContents()) {
            if (t instanceof KSequence) {
                children.add(t);
            }
        }

        if (children.size() == 0 || children.size() == amb.getContents().size())
            return super.visit(amb, _void);
        if (children.size() == 1)
            return this.visitNode(children.get(0));
        amb.setContents(children);
        return super.visit(amb, _void);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _void) throws ParseFailedException {
        assert tc.getProduction() != null : this.getClass() + ":" + " production not found." + tc;
        if (tc.getProduction().isListDecl()) {
            for (int i = 0; i < tc.getContents().size(); i++) {
                tc.getContents().set(i, (Term) secondFilter.visitNode(tc.getContents().get(i)));
            }
        } else if (!tc.getProduction().isConstant() && !tc.getProduction().isSyntacticSubsort()) {
            for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
                if (tc.getProduction().getItems().get(i) instanceof NonTerminal) {
                    // look for the outermost element
                    if (i == 0 || i == tc.getProduction().getItems().size() - 1) {
                        tc.getContents().set(j, (Term) secondFilter.visitNode(tc.getContents().get(j)));
                    }
                    j++;
                }
            }
        }

        return super.visit(tc, _void);
    }

    /**
     * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a KSequence
     *
     * if found, throw an exception and until an Ambiguity node catches it
     *
     * @author Radu
     *
     */
    public class CorrectKSeqFilter2 extends LocalTransformer {
        public CorrectKSeqFilter2(Context context) {
            super("org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter2", context);
        }

        @Override
        public ASTNode visit(KSequence ks, Void _void) throws ParseFailedException {
            /* TODO: andreis changed here; radu please review */
            if (ks.isEmpty()) {
                return super.visit(ks, _void);
            }
            String msg = "Due to typing errors, ~> is not greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getSource(), ks.getLocation());
            throw new PriorityException(kex);
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
