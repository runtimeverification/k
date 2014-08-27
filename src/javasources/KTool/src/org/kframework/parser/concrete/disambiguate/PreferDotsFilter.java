// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
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
    public ASTNode visit(Rule rl, Void _) throws ParseFailedException {
        if (rl.getBody() instanceof Ambiguity) {
            for (Term t : ((Ambiguity) rl.getBody()).getContents()) {
                if (t instanceof Rewrite)
                    processRW((Rewrite) t);
            }
        }
        if (rl.getBody() instanceof Rewrite) {
            processRW((Rewrite) rl.getBody());
        }

        return super.visit(rl, _);
    }

    private void processRW(Rewrite node) throws ParseFailedException {
        // if the left hand side is a function, check to see if the right hand side has the same sort
        if (node.getLeft() instanceof TermCons && ((TermCons) node.getLeft()).getProduction().containsAttribute("function")) {
            Term right = (Term) new TypeSystemFilter2(node.getLeft().getSort(), context).visitNode(node.getRight());
            node.setRight(right, context);
            node.setSort(node.getLeft().getSort());
        }
    }

    @Override
    public ASTNode visit(Cell cell, Void _) throws ParseFailedException {
        Sort sort = context.getCellSort(cell);
        if (sort != null) {
            cell.setContents((Term) preferStrict(sort, cell.getContents()));
        } else {
            String msg = "Cell '" + cell.getLabel() + "' was not declared in a configuration.";
            throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, getName(), cell.getSource(), cell.getLocation()));
        }
        return super.visit(cell, _);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        // choose only the allowed subsorts for a TermCons
        if (tc.getProduction().isListDecl()) {
            UserList ulist = tc.getProduction().getListDecl();
            tc.getContents().set(0, (Term) preferStrict(ulist.getSort(), tc.getContents().get(0)));
            tc.getContents().set(1, (Term) preferStrict(tc.getProduction().getSort(), tc.getContents().get(1)));
        } else {
            int j = 0;
            for (int i = 0; i < tc.getContents().size(); i++) {
                tc.getContents().set(i, (Term) new TypeSystemFilter2(tc.getProduction().getChildSort(i), context).visitNode(tc.getContents().get(i)));
            }
        }

        return super.visit(tc, _);
    }

    @Override
    public ASTNode visit(Cast cast, Void _) throws ParseFailedException {
        cast.setContent((Term) preferStrict(cast.getInnerSort(), cast.getContent()));
        return super.visit(cast, _);
    }

    /**
     * Given the context from the visitor, match on an ambiguity node, and choose only those terms
     * that have exactly the sort of the context. If the result is 0, keep the original ambiguity.
     */
    private ASTNode preferStrict(Sort expectedSort, Term t) {
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
