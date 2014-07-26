// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.KSorts;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort2;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

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
    public Void visit(Syntax node, Void _) {
        String msg = "Multiple top sorts found for " + node.getSort() + ": ";
        int count = 0;
        if (context.isSubsorted(Sort2.KLIST, node.getSort().getSort2())) {
            msg += KSorts.KLIST + ", ";
            count++;
        }
        if (context.isSubsorted(Sort2.LIST, node.getSort().getSort2())) {
            msg += "List, ";
            count++;
        }
        if (context.isSubsorted(Sort2.BAG, node.getSort().getSort2())) {
            msg += "Bag, ";
            count++;
        }
        if (context.isSubsorted(Sort2.MAP, node.getSort().getSort2())) {
            msg += "Map, ";
            count++;
        }
        if (context.isSubsorted(Sort2.SET, node.getSort().getSort2())) {
            msg += "Set, ";
            count++;
        }
        if (count > 1) {
            msg = msg.substring(0, msg.length() - 2);
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _) {
        // optimization to not visit the entire tree
        return null;
    }
}
