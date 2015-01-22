// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * Check for various errors in syntax declarations. 1. You are not allowed to use empty terminals ("") in definitions. You need to have at least two sorts, or a non empty terminal.
 *
 * @author Radu
 *
 */
public class CheckSortTopUniqueness extends BasicVisitor {
    public CheckSortTopUniqueness(Context context) {
        super(context);
    }

    @Override
    public Void visit(Syntax node, Void _void) {
        String msg = "Multiple top sorts found for " + node.getDeclaredSort() + ": ";
        int count = 0;
        if (context.isSubsorted(Sort.KLIST, node.getDeclaredSort().getSort())) {
            msg += Sort.KLIST + ", ";
            count++;
        }
        if (context.isSubsorted(Sort.BAG, node.getDeclaredSort().getSort())) {
            msg += "Bag, ";
            count++;
        }
        if (count > 1) {
            msg = msg.substring(0, msg.length() - 2);
            throw KExceptionManager.compilerError(msg, this, node);
        }
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _void) {
        // optimization to not visit the entire tree
        return null;
    }
}
