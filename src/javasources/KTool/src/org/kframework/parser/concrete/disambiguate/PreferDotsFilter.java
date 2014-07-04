// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.KSorts;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;

public class PreferDotsFilter extends ParseForestTransformer {

    public PreferDotsFilter(Context context) {
        super("Cell types", context);
    }

    // don't do anything for configuration and syntax
    @Override
    public ASTNode visit(Configuration cell, Void _) {
        return cell;
    }

    @Override
    public ASTNode visit(Syntax cell, Void _) {
        return cell;
    }

    @Override
    public ASTNode visit(Cell cell, Void _) throws ParseFailedException {
        String sort = context.cellSorts.get(cell.getLabel());
        // if the k cell is opened, then the sort should be K because of ... desugaring
        if (cell.getLabel().equals("k") && cell.getEllipses() != Ellipses.NONE)
            sort = KSorts.K;

        if (sort == null) {
            if (cell.getLabel().equals("k"))
                sort = "K";
            else if (cell.getLabel().equals("T"))
                sort = "Bag";
            else if (cell.getLabel().equals("generatedTop"))
                sort = "Bag";
            else if (cell.getLabel().equals("freshCounter"))
                sort = "K";
            else if (cell.getLabel().equals(MetaK.Constants.pathCondition))
                sort = "K";
        }

        if (sort != null) {
            cell.setContents((Term) new CellTypesFilter2(sort, context).visitNode(cell.getContents()));
        } else {
            String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), cell.getFilename(), cell.getLocation()));
        }
        return super.visit(cell, _);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        // choose only the allowed subsorts for a TermCons
        if (!tc.getProduction().getItems().isEmpty() && tc.getProduction().getItems().get(0) instanceof UserList) {
            UserList ulist = (UserList) tc.getProduction().getItems().get(0);
            tc.getContents().set(0, (Term) new CellTypesFilter2(ulist.getSort(), context).visitNode(tc.getContents().get(0)));
            tc.getContents().set(1, (Term) new CellTypesFilter2(tc.getProduction().getSort(), context).visitNode(tc.getContents().get(1)));
        } else {
            int j = 0;
            Production prd = tc.getProduction();
            for (int i = 0; i < prd.getItems().size(); i++) {
                if (prd.getItems().get(i) instanceof Sort) {
                    Sort sort = (Sort) prd.getItems().get(i);
                    Term child = (Term) tc.getContents().get(j);
                    tc.getContents().set(j, (Term) new TypeSystemFilter2(sort.getName(), context).visitNode(child));
                    j++;
                }
            }
        }

        return super.visit(tc, _);
    }

    @Override
    public ASTNode visit(Cast cast, Void _) throws ParseFailedException {
        cast.setContent((Term) new TypeSystemFilter2(cast.getInnerSort(), context).visitNode(cast.getContent()));
        return super.visit(cast, _);
    }
    /**
     * A new class (nested) that goes down one level (jumps over Ambiguity) and checks to see if there is a KSequence
     * 
     * if found, throw an exception and until an Ambiguity node catches it
     * 
     * @author Radu
     * 
     */
    public class CellTypesFilter2 extends LocalTransformer {
        String expectedSort;

        public CellTypesFilter2(String expectedSort, Context context) {
            super("org.kframework.parser.concrete.disambiguate.CellTypesFilter2", context);
            this.expectedSort = expectedSort;
        }

        @Override
        public ASTNode visit(Term trm, Void _) throws ParseFailedException {
            // accept only terms that have sort <= to the cell type, or terms of sort K
            if (!context.isSubsortedEq(expectedSort, trm.getSort()) &&
                !(trm.getSort().equals(KSorts.K) && context.isSubsortedEq(KSorts.K, expectedSort))) {
                // if the found sort is not a subsort of what I was expecting
                String msg = "Wrong type in cell '" + "'. Expected sort: " + expectedSort + " but found " + trm.getSort();
                throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), trm.getFilename(), trm.getLocation()));
            }
            return trm;
        }

        @Override
        public ASTNode visit(Bracket node, Void _) throws ParseFailedException {
            node.setContent((Term) this.visitNode(node.getContent()));
            return node;
        }

        @Override
        public ASTNode visit(Rewrite node, Void _) throws ParseFailedException {
            Rewrite result = new Rewrite(node);
            result.setSort(expectedSort);
            result.replaceChildren((Term) this.visitNode(node.getLeft()), (Term) this.visitNode(node.getRight()), context);
            // if the left hand side is a function, check to see if the right hand side has the same sort
            if (node.getLeft() instanceof TermCons && ((TermCons) node.getLeft()).getProduction().containsAttribute("function")) {
                TypeSystemFilter2 tsf = new TypeSystemFilter2(node.getLeft().getSort(), context);
                node.setRight((Term) tsf.visitNode(node.getRight()), context);
                result.setSort(node.getLeft().getSort());
            }

            return result;
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
            // try to be greedy and select only the terms that are directly subsorted to the cell sort
            ArrayList<Term> subsorted = new ArrayList<>();
            for (Term trm : node.getContents()) {
                if (trm instanceof ListTerminator && context.isSubsortedEq(expectedSort, trm.getSort()))
                    subsorted.add(trm);
            }
            if (subsorted.size() > 0)
                node.setContents(subsorted);
            else
                node.setContents(terms);
            return node;
        }
    }
}
