// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Configuration;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSorts;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.PriorityException;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CorrectRewritePriorityFilter extends ParseForestTransformer {
    private CorrectRewriteFilter2 secondFilter;

    public CorrectRewritePriorityFilter(Context context) {
        super("Correct Rewrite priority", context);
        secondFilter = new CorrectRewriteFilter2(context);
    }

    @Override
    public ASTNode visit(Configuration cfg, Void _) throws ParseFailedException {
        return cfg;
    }

    @Override
    public ASTNode visit(Syntax syn, Void _) throws ParseFailedException {
        return syn;
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _) throws ParseFailedException {
        List<Term> children = new ArrayList<Term>();
        boolean klist = false;
        Term krw = null;
        for (Term t : amb.getContents()) {
            if (t instanceof Rewrite) {
                if (t.getSort().equals(KSorts.KLIST))
                    klist = true;
                if (t.getSort().equals(KSorts.K))
                    krw = t;
                children.add(t);
            }
        }
        if (klist)
            children.remove(krw);

        if (children.size() == 0 || children.size() == amb.getContents().size())
            return super.visit(amb, _);
        if (children.size() == 1)
            return this.visitNode(children.get(0));
        amb.setContents(children);
        return super.visit(amb, _);
    }

    @Override
    public ASTNode visit(KSequence ks, Void _) throws ParseFailedException {
        if (ks.getContents().size() == 2) {
            ks.getContents().set(0, (Term) secondFilter.visitNode(ks.getContents().get(0)));
            ks.getContents().set(1, (Term) secondFilter.visitNode(ks.getContents().get(1)));
        }
        assert ks.getContents().size() <= 2;

        return super.visit(ks, _);
    }

    @Override
    public ASTNode visit(KList ks, Void _) throws ParseFailedException {
        if (ks.getContents().size() == 2) {
            ks.getContents().set(0, (Term) secondFilter.visitNode(ks.getContents().get(0)));
            ks.getContents().set(1, (Term) secondFilter.visitNode(ks.getContents().get(1)));
        }
        assert ks.getContents().size() <= 2;

        return super.visit(ks, _);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        if (tc.getProduction() == null)
            System.err.println(this.getClass() + ":" + " cons not found." + tc.getCons());
        if (tc.getProduction().isListDecl()) {
            tc.getContents().set(0, (Term) secondFilter.visitNode(tc.getContents().get(0)));
            tc.getContents().set(1, (Term) secondFilter.visitNode(tc.getContents().get(1)));
        } else if (!tc.getProduction().isConstant() && !tc.getProduction().isSubsort()) {
            for (int i = 0, j = 0; i < tc.getProduction().getItems().size(); i++) {
                if (tc.getProduction().getItems().get(i) instanceof Sort) {
                    // look for the outermost element
                    if (i == 0 || i == tc.getProduction().getItems().size() - 1) {
                        tc.getContents().set(j, (Term) secondFilter.visitNode(tc.getContents().get(j)));
                    }
                    j++;
                }
            }
        }

        return super.visit(tc, _);
    }

    /**
     * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a KSequence
     * 
     * if found, throw an exception and until an Ambiguity node catches it
     * 
     * @author Radu
     * 
     */
    public class CorrectRewriteFilter2 extends LocalTransformer {
        public CorrectRewriteFilter2(Context context) {
            super("org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter2", context);
        }

        @Override
        public ASTNode visit(Rewrite ks, Void _) throws ParseFailedException {
            String msg = "Due to typing errors, => is not greedy. Use parentheses to set proper scope.";
            KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, ks.getFilename(), ks.getLocation());
            throw new PriorityException(kex);
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
