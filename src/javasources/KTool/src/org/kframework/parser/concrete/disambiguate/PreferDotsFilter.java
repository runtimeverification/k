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
        super(PreferDotsFilter.class.getName(), context);
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
            cell.setContents((Term) prefer(sort, cell.getContents()));
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
            tc.getContents().set(0, (Term) prefer(ulist.getSort(), tc.getContents().get(0)));
            tc.getContents().set(1, (Term) prefer(tc.getProduction().getSort(), tc.getContents().get(1)));
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
        cast.setContent((Term) prefer(cast.getInnerSort(), cast.getContent()));
        return super.visit(cast, _);
    }

    /**
     * Given the context from the visitor, match on an ambiguity node, and choose only those terms
     * that have exactly the sort of the context. If the result is 0, keep the original ambiguity.
     */
    private ASTNode prefer(String expectedSort, Term t) {
        if (t instanceof Ambiguity) {
            Ambiguity node = (Ambiguity) t;
            ArrayList<Term> eqSort = new ArrayList<>();

            for (Term trm : node.getContents()) {
                if (trm instanceof ListTerminator && expectedSort.equals(trm.getSort()))
                    eqSort.add(trm);
            }
            if (eqSort.size() == 0)
                return t;
            else if (eqSort.size() == 1)
                return eqSort.get(0);
            node.setContents(eqSort);
            return node;
        }
        return t;
    }
}
