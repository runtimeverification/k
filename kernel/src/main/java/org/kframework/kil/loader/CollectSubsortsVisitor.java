// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.UserList;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectSubsortsVisitor extends BasicVisitor {

    public CollectSubsortsVisitor(Context context) {
        super(context);
    }

    public Void visit(Definition def, Void _void) {
        super.visit(def, _void);
        context.computeSubsortTransitiveClosure();
        return null;
    }

    public Void visit(Syntax syn, Void _void) {
        Sort sort = syn.getDeclaredSort().getSort();
        if (!sort.isBaseSort()) {
            context.addSubsort(Sort.KITEM, sort);
            context.addSyntacticSubsort(Sort.KITEM, sort);
        }
        return super.visit(syn, _void);
    }

    public Void visit(Production prd, Void _void) {
        if (prd.isSubsort()) {
            context.addSubsort(prd.getSort(), prd.getSubsort());
        }

        if (!prd.getSort().isBaseSort())
            context.addSyntacticSubsort(Sort.KITEM, prd.getSort());
        if (prd.isSyntacticSubsort()) {
            if (!prd.containsAttribute("onlyLabel")
                    && !prd.containsAttribute("notInRules")) {
                Sort sort = ((NonTerminal) prd.getItems().get(0)).getSort();
                context.addSyntacticSubsort(prd.getSort(), sort);
            }
        } else if (prd.isListDecl()) {
            UserList srt = (UserList) prd.getItems().get(0);
            context.addSyntacticSubsort(prd.getSort(), srt.getSort());
        } else {
            for (ProductionItem pi : prd.getItems()) {
                if (pi instanceof NonTerminal) {
                    Sort s = ((NonTerminal) pi).getSort();
                    if (!s.isBaseSort())
                        context.addSyntacticSubsort(Sort.KITEM, s);
                }
            }
        }
        return null;
    }
}
