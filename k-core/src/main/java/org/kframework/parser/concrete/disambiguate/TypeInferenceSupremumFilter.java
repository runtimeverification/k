// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Lexical;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;

public class TypeInferenceSupremumFilter extends ParseForestTransformer {

    public TypeInferenceSupremumFilter(Context context) {
        super("Type inference supremum", context);
    }

    @Override
    public ASTNode visit(Ambiguity amb, Void _) throws ParseFailedException {
        // find the groups of terms alike

        Set<Term> processed = new HashSet<Term>();
        Set<Term> maxterms = new HashSet<Term>();
        for (Term t : amb.getContents()) {
            if (!processed.contains(t)) {
                processed.add(t);
                Set<Term> group = new HashSet<Term>();
                group.add(t);
                for (Term t2 : amb.getContents()) {
                    if (!processed.contains(t2) && termsAlike_simple(t, t2)) {
                        processed.add(t2);
                        group.add(t2);
                    }
                }

                // found a group of terms that are alike
                // alike means they have the same arity, same position for terminals and non terminals
                if (t instanceof TermCons) {
                    // finally, try to find the <strike> maximum </strike> minimum
                    for (Term tm2 : group) {
                        boolean max = true;
                        Production tcBig = ((TermCons) tm2).getProduction();
                        for (Term tm22 : group) {
                            Production tcSmall = ((TermCons) tm22).getProduction();
                            if (tm2 != tm22 && isSubsorted(tcSmall, tcBig)) {
                                max = false;
                                break;
                            }
                        }
                        if (max)
                            maxterms.add(tm2);
                    }
                } else if (t instanceof Variable || t instanceof ListTerminator) {
                    // for variables only, find maximum
                    for (Term t1 : group) {
                        boolean max = true;
                        for (Term t2 : group)
                            if (t1 != t2 && context.isSyntacticSubsorted(t2.getSort(), t1.getSort()))
                                max = false;
                        if (max)
                            maxterms.add(t1);
                    }
                } else
                    maxterms.addAll(group);
            }
        }

        if (maxterms.size() == 1) {
            return this.visitNode(maxterms.iterator().next());
        } else if (maxterms.size() > 1)
            amb.setContents(new ArrayList<Term>(maxterms));

        return super.visit(amb, _);
    }

    private boolean isSubsorted(Production big, Production small) {
        if (big == small)
            return false;
        if (big.getItems().size() != small.getItems().size())
            return false;
        if (!context.isSyntacticSubsortedEq(big.getSort(), small.getSort()))
            return false;
        for (int i = 0; i < big.getItems().size(); i++) {
            if (!(big.getItems().get(i) instanceof Terminal && small.getItems().get(i) instanceof Terminal) &&
                !(big.getItems().get(i) instanceof NonTerminal && small.getItems().get(i) instanceof NonTerminal) &&
                !(big.getItems().get(i) instanceof UserList && small.getItems().get(i) instanceof UserList) &&
                !(big.getItems().get(i) instanceof Lexical && small.getItems().get(i) instanceof Lexical)) {
                return false;
            } else if (big.getItems().get(i) instanceof NonTerminal) {
                Sort bigSort = ((NonTerminal) big.getItems().get(i)).getSort();
                Sort smallSort = ((NonTerminal) small.getItems().get(i)).getSort();
                if (!context.isSyntacticSubsortedEq(bigSort, smallSort))
                    return false;
            } else if (big.getItems().get(i) instanceof UserList) {
                Sort bigSort = ((UserList) big.getItems().get(i)).getSort();
                Sort smallSort = ((UserList) small.getItems().get(i)).getSort();
                if (!context.isSyntacticSubsortedEq(bigSort, smallSort))
                    return false;
            } else
                continue;
        }
        return true;
    }

    private boolean termsAlike_simple(Term trm1, Term trm2) {
        if (!trm1.getClass().equals(trm2.getClass()))
            return false;

        if (trm1 instanceof TermCons) {
            TermCons term1 = (TermCons) trm1;
            TermCons term2 = (TermCons) trm2;

            // check to see if the two terms have the same arity
            if (term1.getProduction().getItems().size() != term2.getProduction().getItems().size())
                return false;

            if (!term1.getProduction().getKLabel().equals(term2.getProduction().getKLabel()))
                return false;

            for (int i = 0; i < term1.getProduction().getItems().size(); i++) {
                ProductionItem itm1 = term1.getProduction().getItems().get(i);
                ProductionItem itm2 = term2.getProduction().getItems().get(i);

                if (itm1 instanceof Terminal && !itm1.equals(itm2))
                    return false;
                else if (itm1 instanceof UserList) {
                    if (!(itm2 instanceof UserList))
                        return false;
                    UserList ul1 = (UserList) itm1;
                    UserList ul2 = (UserList) itm2;

                    if (!ul1.getSeparator().equals(ul2.getSeparator()))
                        return false;
                } else if (itm1 instanceof NonTerminal) {
                    if (!(itm2 instanceof NonTerminal))
                        return false;
                }
            }
        }

        return true;
    }
}
