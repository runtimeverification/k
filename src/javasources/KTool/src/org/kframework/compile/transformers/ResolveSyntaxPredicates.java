// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ResolveSyntaxPredicates extends CopyOnWriteTransformer {



    public ResolveSyntaxPredicates(org.kframework.kil.loader.Context context) {
        super("Resolve syntax predicates", context);
    }


    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Sentence node, Void _)  {
        boolean change = false;
        List<Variable> vars = new ArrayList<>(node.getBody().variables());
        // if we kept it as a set then the order of side conditions in maude would be dependent on
        // the iteration order of a set, which is JVM dependent. So we sort the list first.
        Collections.sort(vars);
        KList ands = new KList();
        Term condition = node.getRequires();
        if (null != condition) {
            ands.getContents().add(condition);
        }
        for (Variable var : vars) {
//            if (!var.isUserTyped()) continue;
            if (var.isFreshConstant()) continue;
            if (var.isSyntactic()) continue;
            if (var.getSort().isKSort()) continue;
            change = true;
            ands.getContents().add(getPredicateTerm(var));
        }
        if (!change) return node;
        if (ands.getContents().size() > 1) {
            condition = new KApp(KLabelConstant.ANDBOOL_KLABEL, ands);
        } else {
            condition = ands.getContents().get(0);
        }
        node = node.shallowCopy();
        node.setRequires(condition);
        return node;
    }

    private Term getPredicateTerm(Variable var) {
        return KApp.of(KLabelConstant.of(AddPredicates.predicate(var.getSort()), context), var);
    }

}
