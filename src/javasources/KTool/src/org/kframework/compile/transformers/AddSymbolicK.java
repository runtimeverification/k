// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
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
        Sort2 sort = Sort2.of(sortName);
        return MetaK.isComputationSort(sort) && !MetaK.isBuiltinSort(sort);
    }

    public static final String symbolicConstructor(String sort) {
        assert allowSymbolic(sort);

            return SymbolicConstructorPrefix + sort;
    }

    public static final boolean isSymbolicConstructor(String sort) {
        return sort.startsWith(SymbolicConstructorPrefix);
    }

    public final Production getSymbolicProduction(String sort) {
        assert allowSymbolic(sort);

        return Production.makeFunction(sort, symbolicConstructor(sort), KSorts.K, context);
    }

    public final Term makeSymbolicTerm(Sort2 sort, Term term) {
        assert allowSymbolic(sort.getName());

        String ctor = symbolicConstructor(sort.getName());
        Term symTerm;
        if (!allowKSymbolic(sort.getName())) {
            symTerm = new TermCons(sort, ctor, context);
            ((TermCons) symTerm).getContents().add(term);
        } else {
            symTerm = KApp.of(KLabelConstant.of(ctor, context), term);
        }

        return symTerm;
    }

    public Term freshSymSortN(Sort2 sort, int n) {
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

        for (String sort : node.getAllSorts()) {
            if (allowKSymbolic(sort)) {
                //retNode.addProduction(sort, getSymbolicProduction(sort));
                retNode.addConstant(KSorts.KLABEL, symbolicConstructor(sort));
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

