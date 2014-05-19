// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class MakeFreshVariables extends CopyOnWriteTransformer {

    private List<Variable> variables;

    public MakeFreshVariables(Context context, List<Variable> vars) {
        super("Replace a list of variables with symbolic values", context);
        this.variables = vars;
    }

    @Override
    public ASTNode visit(Variable node, Void _)  {
//        System.out.println("Var: " + node + " sort: " + node.getSort()
//                + " is fresh " + node.isFreshVariable());
        for (Variable v : variables) {
            if (v.getName().equals(node.getName()) && !node.isFreshVariable()) {
//                System.out.println("Transformed: " + node + "(" + v.getSort()
//                        + ", " + node.isFreshVariable() + ")");
                //return new AddSymbolicK(context).freshSymSortN(v.getSort(),
                //        RLBackend.idx);
                return KApp.of(KLabelConstant.of(AddSymbolicK.symbolicConstructor(v.getSort())), Token.kAppOf("#Id", v.getName()));
            }
        }
        return super.visit(node, _);
    }
}
