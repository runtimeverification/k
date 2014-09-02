// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.*;
import java.util.List;
import java.util.Set;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 12/4/13
 * Time: 2:02 PM
 * To change this template use File | Settings | File Templates.
 */
public class CheckSmtLibByAddingPredicates extends BasicVisitor{
    private boolean smtValid = false;
    private List<Term> contents;

    public CheckSmtLibByAddingPredicates(Context context) {
        super(context);
        contents = new ArrayList<>();
    }

    @Override
    public Void visit(KApp node, Void _) {
        Term klabel = node.getLabel();

        if (klabel instanceof KLabelConstant) {
            if (klabel.equals(KLabelConstant.KEQ)) {
                smtValid = true;
                return null;
            }

            Set<Production> prods = context.klabels.get(((KLabelConstant) klabel).getLabel());
            if (prods == null) {
                smtValid = false;
            } else {
                Iterator<Production> it = prods.iterator();
                while (it.hasNext()) {
                    Production p = it.next();
                    if (p.containsAttribute("smtlib") || p.containsAttribute("symbolic-function")) {
                        smtValid = true;
                        if (node.getChild() instanceof  KList) {
                            KList children = (KList) node.getChild();
                            int i = 0;
                            for (Term child: children.getContents()) {
                                String predicateString = AddPredicates.predicate(p.getChildSort(i));
                                i++;
                                KLabelConstant kLabel = KLabelConstant.of(predicateString);
                                contents.add(KApp.of(kLabel, child));
                            }
                        }
                    }
                    else {
                        smtValid = false;
                    }

                    // only first production assumed
                    break;
                }
            }
        }
        // super.visit(node, _);
        return null;
    }

    public boolean smtValid() {
        return smtValid;
    }

    public List<Term> getContents() {
        return contents;
    }
}
