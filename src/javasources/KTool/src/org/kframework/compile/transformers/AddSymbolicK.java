// Copyright (c) 2012-2014 K Team. All Rights Reserved.
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

    public static final boolean allowSymbolic(String sort) {
        return sort.equals(KSorts.LIST) || sort.equals(KSorts.SET) ||
                sort.equals(KSorts.BAG) || sort.equals(KSorts.MAP) ||
                allowKSymbolic(sort);
    }

    public static final boolean allowKSymbolic(String sortName) {
        Sort sort = Sort.of(sortName);
        return sort.isComputationSort() && !sort.isBuiltinSort();
    }

    public static final String symbolicConstructor(String sort) {
        assert allowSymbolic(sort);

            return SymbolicConstructorPrefix + sort;
    }

    public static final boolean isSymbolicConstructor(String sort) {
        return sort.startsWith(SymbolicConstructorPrefix);
    }

    public final Production getSymbolicProduction(String sortName) {
        assert allowSymbolic(sortName);

        return Production.makeFunction(Sort.of(sortName), symbolicConstructor(sortName), Sort.K, context);
    }

    public Term freshSymSortN(Sort sort, int n) {
        return KApp.of(
                KLabelConstant.of("'#freshSymSortN", context),
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
    public ASTNode visit(Module node, Void _)  {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (Sort sort : node.getAllSorts()) {
            if (allowKSymbolic(sort.getName())) {
                //retNode.addProduction(sort, getSymbolicProduction(sort));
                retNode.addConstant(Sort.KLABEL, symbolicConstructor(sort.getName()));
            }
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

    public static String getSymbolicConstructorPrefix() {
        return SymbolicConstructorPrefix;
    }
}

