// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;


public class AddSymbolicK extends CopyOnWriteTransformer {

    private static final String SymbolicConstructorPrefix = "#sym";

    public AddSymbolicK(Context context) {
        super("Add symbolic constructors", context);
    }

    public static final boolean allowSymbolic(Sort sort) {
        return sort.equals(Sort.LIST) || sort.equals(Sort.SET) ||
                sort.equals(Sort.BAG) || sort.equals(Sort.MAP) ||
                allowKSymbolic(sort);
    }

    public static final boolean allowKSymbolic(Sort sort) {
        return sort.isComputationSort() && !sort.isBuiltinSort();
    }

    public static final String symbolicConstructor(Sort sort) {
        assert allowSymbolic(sort);

            return SymbolicConstructorPrefix + sort;
    }

    public Term freshSymSortN(Sort sort, int n) {
        return KApp.of(
                KLabelConstant.of("'#freshSymSortN"),
                StringBuiltin.kAppOf(sort.getName()),
                IntBuiltin.kAppOf(n));
    }

//    public Term freshSymSortId(String sort, String id) {
//        return KApp.of(
//                KLabelConstant.of("'#freshSymSortN", context),
//                StringBuiltin.kAppOf(sort),
//                StringBuiltin.kAppOf(id));
//    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (Sort sort : node.getAllSorts()) {
            if (allowKSymbolic(sort)) {
                //retNode.addProduction(sort, getSymbolicProduction(sort));
                retNode.addConstant(Sort.KLABEL, symbolicConstructor(sort));
            }
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }
}

