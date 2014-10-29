// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.HashMap;
import java.util.Map;

/*
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 11/21/12
 * Time: 3:13 PM
 */

/**
 * Checks Variable consistency.
 *
 * Generic variables:
 * 1. Variables must be bound in the pattern
 * 2. Variables unused in the rhs should be anonymous.
 *
 * Fresh variables:
 * 1. fresh can only appear as a side condition
 * 2. fresh can only be applied to a variable
 * 3. the fresh variable can only appear as a replacement variable
 *
 * Matching logic (option -ml): named variables may appear in the rhs
 */
public class CheckVariables extends BasicVisitor {

    private final KExceptionManager kem;

    public CheckVariables(Context context, KExceptionManager kem) {
        super(context);
        this.kem = kem;
    }

    HashMap<Variable, Integer> left = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> right = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> fresh = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> current = left;
    boolean inCondition = false;

    @Override
    public Void visit(Rewrite node, Void _) {
        this.visitNode(node.getLeft());
        current = right;
        this.visitNode(node.getRight());
        current = left;
        return null;
    }

    @Override
    public Void visit(Variable node, Void _) {
        boolean freshConstant = node.isFreshConstant();
        if (node.isFreshVariable() || freshConstant) {
            if (freshConstant && !context.freshFunctionNames.containsKey(node.getSort())) {
                throw KExceptionManager.compilerError(
                        "Unsupported sort of fresh variable: " + node.getSort()
                                + "\nOnly sorts "
                                + context.freshFunctionNames.keySet()
                                + " admit fresh variables.", this, node);
            }

            if (current == right  && !inCondition) {
                 Integer i = fresh.get(node);
                 if (i == null) i = new Integer(1);
                 else i = new Integer(i.intValue());
                 fresh.put(node, i);
                 return null;
             }
             //nodes are ok to be found in rhs
             throw KExceptionManager.compilerError(
                    "Fresh variable \"" + node + "\" is bound in the " + "rule pattern.",
                    this, node);
        }
//        System.out.println("Variable: " + node);
        Integer i = current.remove(node);
        if (i == null) {
            i = new Integer(1);
        } else {
            i = new Integer(i.intValue() + 1);
        }
        current.put(node, i);
        return null;
    }

    @Override
    public Void visit(Configuration node, Void _) {
        return null;
    }

    @Override
    public Void visit(Syntax node, Void _) {
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _) {
        inCondition = false;
        left.clear();
        right.clear();
        fresh.clear();
        current = left;
        this.visitNode(node.getBody());
        if (node.getRequires() != null) {
            current = right;
            inCondition = true;
            this.visitNode(node.getRequires());
        }
        //TODO: add checks for Ensures, too.
        for (Variable v : right.keySet()) {
            if (MetaK.isAnonVar(v) && !(v.isFreshVariable() || v.isFreshConstant())) {
                throw KExceptionManager.compilerError(
                        "Anonymous variable found in the right hand side of a rewrite.",
                        this, v);
            }
            if (!left.containsKey(v)) {
                throw KExceptionManager.compilerError(
                        "Unbounded variable " + v.toString() + "should start with ? or !.",
                        this, v);
            }
        }
        for (Map.Entry<Variable,Integer> e : left.entrySet()) {
            final Variable key = e.getKey();
            if (fresh.containsKey(key)) {
                throw KExceptionManager.compilerError(
                        "Variable " + key + " has the same name as a fresh variable.",
                        this, key);
            }
            if (MetaK.isAnonVar(key)) continue;
            if (e.getValue().intValue() > 1) continue;
            if (!right.containsKey(key)) {
                kem.register(new KException(KException.ExceptionType.HIDDENWARNING,
                        KException.KExceptionGroup.COMPILER,
                        "Singleton variable " + key.toString() + ".\n" +
                        "    If this is not a spelling mistake, please consider using anonymous variables.",
                        getName(), key.getSource(), key.getLocation()));
            }
        }
        return null;
    }
}
