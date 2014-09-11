// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class CellTypesFilter extends ParseForestTransformer {

    public CellTypesFilter(org.kframework.kil.loader.Context context) {
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
        Sort sort = context.getCellSort(cell);

        if (sort != null) {
            cell.setContents((Term) new CellTypesFilter2(context, sort, cell.getLabel()).visitNode(cell.getContents()));
        } else {
            String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), cell.getSource(), cell.getLocation()));
        }
        return super.visit(cell, _);
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
        Sort expectedSort;
        String cellLabel;

        public CellTypesFilter2(Context context, Sort expectedSort, String cellLabel) {
            super(CellTypesFilter2.class.getName(), context);
            this.expectedSort = expectedSort;
            this.cellLabel = cellLabel;
        }

        @Override
        public ASTNode visit(Term trm, Void _) throws ParseFailedException {
            if (!context.isSyntacticSubsortedEq(expectedSort, trm.getSort()) &&
                !(context.isSyntacticSubsortedEq(Sort.KLIST, expectedSort) &&
                                (trm.getSort().equals(Sort.KLIST) ||
                                trm.getSort().equals(Sort.K) ||
                                trm.getSort().equals(Sort.KITEM)))) {
                // if the found sort is not a subsort of what I was expecting
                String msg = "Wrong type in cell '" + cellLabel + "'. Expected sort: " + expectedSort + " but found " + trm.getSort();
                throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), trm.getSource(), trm.getLocation()));
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
            node.setContents(terms);
            return node;
        }
    }
}
