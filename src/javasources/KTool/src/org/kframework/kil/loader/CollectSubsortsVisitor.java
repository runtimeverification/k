// Copyright (c) 2012-2014 K Team. All Rights Reserved.
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

    public Void visit(Definition def, Void _) {
        super.visit(def, _);
        context.computeSubsortTransitiveClosure();
        return null;
    }

    public Void visit(Syntax syn, Void _) {
        if (syn.getPriorityBlocks().size() == 0) {
            Sort sort = syn.getDeclaredSort().getSort();
            if (!sort.equals(Sort.KITEM)) {
                context.addSubsort(Sort.KITEM, sort);
            }
        }
        return super.visit(syn, _);
    }

    public Void visit(Production prd, Void _) {
        if (!prd.getSort().isBaseSort())
            context.addSubsort(Sort.KITEM, prd.getSort());
        if (prd.isSubsort()) {
            if (!prd.containsAttribute("onlyLabel")
                    && !prd.containsAttribute("notInRules")) {
                Sort sort = ((NonTerminal) prd.getItems().get(0)).getSort();
                context.addSubsort(prd.getSort(), sort);
            }
        } else if (prd.isListDecl()) {
            UserList srt = (UserList) prd.getItems().get(0);
            context.addSubsort(prd.getSort(), srt.getSort());
        } else {
            for (ProductionItem pi : prd.getItems()) {
                if (pi instanceof NonTerminal) {
                    Sort s = ((NonTerminal) pi).getSort();
                    if (!s.isBaseSort())
                        context.addSubsort(Sort.KITEM, s);
                }
            }
        }
        return null;
    }
}
