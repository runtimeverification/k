// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashSet;

import org.kframework.attributes.Location;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;


public class MergeAmbFilter extends ParseForestTransformer {
    public MergeAmbFilter(Context context) {
        super("Remove ambiguity duplicates", context);
    }

    /**
     * Restructure a node
     * from: [A(x1, x2 ... xn), A(y1, y2 ... yn), A ..., B]
     * to  : [A(amb([x1, y1, ...]), amb([x2, y2, ...]), ... amb([xn, yn, ...])), B]
     *
     * if the children of every A are located in the same places (see isSimilar(...)).
     */
    @Override
    public ASTNode visit(Ambiguity amb, Void _void) throws ParseFailedException {

        java.util.List<Term> children = new ArrayList<Term>();
        //IStrategoTerm currentList = amb.getSubterm(0);
        for (int i = 0; i < amb.getContents().size(); i++)
            children.add(amb.getContents().get(i));

        java.util.List<Term> newchildren = new ArrayList<Term>();

        // while there are still children that haven't been processed
        while (!children.isEmpty()) {
            // group the similar children
            Term head = children.get(0);
            java.util.List<Term> similar = new ArrayList<Term>();
            similar.add(head);
            for (int i = 1; i < children.size(); i++) {
                if (isSimilar(head, children.get(i))) {
                    similar.add(children.get(i));
                }
            }

            // remove the grouped nodes from the children list
            children.removeAll(similar);

            // create a new node that combines the children in new ambiguity nodes
            if (similar.size() > 1) {
                TermCons tcnew = new TermCons((TermCons) head);
                tcnew.getContents().clear();

                for (int i = 0; i < tcnew.arity(); i++) {
                    java.util.Set<Term> list2 = new HashSet<Term>();
                    for (int j = 0; j < similar.size(); j++)
                        list2.add(((TermCons) similar.get(j)).getContents().get(i));

                    if (list2.size() > 1) {
                        Ambiguity amb2 = new Ambiguity(Sort.K, new ArrayList<Term>(list2));
                        amb2.setLocation(tcnew.getLocation());
                        amb2.setSource(tcnew.getSource());
                        tcnew.getContents().add(amb2);
                    } else
                        tcnew.getContents().add(list2.iterator().next());
                }
                newchildren.add(tcnew);
            } else {
                // if there is only one child, just add it to the new list
                newchildren.add(similar.get(0));
            }
        }

        if (newchildren.size() > 1) {
            Ambiguity amb2 = new Ambiguity(Sort.K, newchildren);
            return super.visit(amb2, _void);
        } else
            return this.visitNode(newchildren.get(0));
    }

    /**
     * Check if two terms are similar. Meaning they have the same constructor, and the children are located in the same places.
     * @param t1 - first term.
     * @param t2 - second term.
     * @param context - the context in which to compare them.
     * @return - true if the terms are similar, false otherwise.
     */
    private boolean isSimilar(Term t1, Term t2) {
        if (!t1.getClass().equals(t2.getClass()))
            return false;

        if (t1 instanceof TermCons) {
            if (!((TermCons) t1).getProduction().equals(((TermCons) t2).getProduction()))
                return false;

            TermCons tc1 = (TermCons) t1;
            TermCons tc2 = (TermCons) t2;
            for (int i = 0; i < tc1.getContents().size(); i++) {
                Location loc1 = tc1.getContents().get(i).getLocation();
                Location loc2 = tc2.getContents().get(i).getLocation();

                if (!loc1.equals(loc2))
                    return false;
            }
            return true;
        }
        return false;
    }
}
