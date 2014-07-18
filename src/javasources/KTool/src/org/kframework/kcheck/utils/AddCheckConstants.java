// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddCheckConstants extends CopyOnWriteTransformer {

    private int n = 0;
    public static final String CHECK = "check";

    public AddCheckConstants(Context context, int n) {
        super("Add check constants for kcheck", context);
        this.n = n;
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (int i = 0; i < n; i++) {
            retNode.addConstant(KSorts.KLABEL, getName(i));
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

    private static String getName(int i) {
        return CHECK + i;
    }

    public static Term getFreshImplicationForRule(int indexOf, Context context) {
        return KApp.of(KLabelConstant.of(getName(indexOf), context), KList.EMPTY);
    }

    public static Term getFreshImplicationForPgm(int indexOf, Context context) {
        return KApp.of(KLabelConstant.of(getName(indexOf), context), KList.EMPTY);
    }
}
