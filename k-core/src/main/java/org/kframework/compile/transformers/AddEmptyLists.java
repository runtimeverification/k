// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.ArrayList;
import java.util.List;

/**
 * Transformer class adding the implicit terminator (.List{"<klabel>"}) to user defined lists.
 */
public class AddEmptyLists extends CopyOnWriteTransformer {

    private final KExceptionManager kem;

    public AddEmptyLists(Context context, KExceptionManager kem) {
        super("Add empty lists", context);
        this.kem = kem;
    }

    /**
     * If expectedSort is a list sort and term t is a single
     * term of the element sort (or a subsort) rather than a list,
     * wrap t into a single-element list.
     * If t is neither a subsort of the expected list sort nor
     * the expected element sort, records a hidden warning.
     * Returns null if t was wrapped.
     *
     * @param t
     * @param expectedSort
     * @return wrapped t, or null if no change should be made
     */
    private Term wrapTerm(Term t, Sort expectedSort) {
        if (isAddEmptyList(context, expectedSort, t.getSort())) {
            if (!isUserListElement(expectedSort, t, context)) {
                String msg = "Found sort '" + t.getSort() + "' where list sort '" + expectedSort + "' was expected. Moving on.";
                kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getSource(), t.getLocation()));
            } else
                return addEmpty(t, expectedSort);
        }
        return null;
    }

    public ASTNode visit(Rewrite r, Void _) {
        Term left = r.getLeft();
        final Sort target;
        if (left instanceof TermCons) {
            Production p = ((TermCons) left).getProduction();
            if (p.containsAttribute(Attribute.FUNCTION_KEY) || p.containsAttribute(Attribute.PREDICATE_KEY)) {
                target = left.getSort();
            } else {
                target = r.getSort();
            }
        } else {
            target = r.getSort();
        }

        left = wrapTerm(r.getLeft(), target);
        if (left != null) {
            r.setLeft(left, context);
        }
        Term right = wrapTerm(r.getRight(), target);
        if (right != null) {
            r.setRight(right, context);
        }
        return super.visit(r, _);
    }

    @Override
    public ASTNode visit(Cell c, Void _) {
        Term t = c.getContents();
        t = wrapTerm(t, context.getCellSort(c));
        if (t != null) {
            c.setContents(t);
        }
        return super.visit(c, _);
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) {
        Production p = tc.getProduction();

        if (p.isListDecl()) {
            Term t = tc.getContents().get(0);
            UserList ul = (UserList) p.getItems().get(0);
            t = wrapTerm(t, ul.getSort());
            if (t != null) {
                tc.getContents().set(0, t);
            }

            // if the term should be a list, append the empty element
            t = tc.getContents().get(1);
            t = wrapTerm(t, p.getSort());
            if (t != null) {
                tc.getContents().set(1, t);
            }
        } else {
            for (int i = 0, j = 0; j < p.getItems().size(); j++) {
                ProductionItem pi = p.getItems().get(j);
                if (!(pi instanceof NonTerminal))
                    continue;

                Sort sort = ((NonTerminal) pi).getSort();
                Term t = tc.getContents().get(i);
                t = wrapTerm(t, sort);
                if (t != null) {
                    tc.getContents().set(i, t);
                }
                i++;
            }
        }

        return super.visit(tc, _);
    }

    private boolean isUserListElement(Sort listSort, Term element, Context context) {
        Sort elementSort = element.getSort();

        /* TODO: properly infer sort of KApp */
        if (elementSort.equals(Sort.KITEM) && element instanceof KApp) {
            /* infer sort for builtins and tokens */
            if (((KApp) element).getLabel() instanceof Token) {
                elementSort = ((Token) ((KApp) element).getLabel()).tokenSort();
            }
        }

        return !elementSort.equals(Sort.KITEM)
               && context.isSubsortedEq(context.getListElementSort(listSort), elementSort);
    }

    public static boolean isAddEmptyList(Context context, Sort expectedSort, Sort termSort) {
        if (!context.isListSort(expectedSort))
            return false;
        if (context.isSubsortedEq(expectedSort, termSort)
                && context.isListSort(termSort))
            return false;
        return true;
    }

    private Term addEmpty(Term node, Sort sort) {
        TermCons tc = new TermCons(sort, getListProduction(sort));
        List<Term> genContents = new ArrayList<Term>();
        genContents.add(node);
        genContents.add(new ListTerminator(sort, null));

        tc.setContents(genContents);
        return tc;
    }

    private Production getListProduction(Sort psort) {
        return context.listProductions.get(psort);
    }
}
