package org.kframework.compile.checks;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kompile.KompileOptions;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

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

    public static final String UNBOUNDED_VARS = "hasUnboundedVars";

    KompileOptions options;
    
    public CheckVariables(Context context) {
        super(context);
        options = context.kompileOptions;
    }

    HashMap<Variable, Integer> left = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> right = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> fresh = new HashMap<Variable, Integer>();
    HashMap<Variable, Integer> current = left;
    boolean inCondition = false;

    @Override
    public void visit(Rewrite node) {
        node.getLeft().accept(this);
        current = right;
        node.getRight().accept(this);
        current = left;
    }

    @Override
    public void visit(Variable node) {
        if (node.isFresh()) {
             if (current == right  && !inCondition) {
                 Integer i = fresh.get(node);
                 if (i == null) i = new Integer(1);
                 else i = new Integer(i.intValue());
                 fresh.put(node, i);
                 return;
             }
             //nodes are ok to be found in rhs
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.COMPILER,
                    "Fresh variable \"" + node + "\" is bound in the " +
                            "rule pattern.",
                    getName(), node.getFilename(), node.getLocation()
            ));
        }
//        System.out.println("Variable: " + node);
        Integer i = current.remove(node);
        if (i == null) {
            i = new Integer(1);
        } else {
            i = new Integer(i.intValue() + 1);
        }
        current.put(node, i);
    }

    @Override
    public void visit(Configuration node) {
        return;
    }

    @Override
    public void visit(Syntax node) {
        return;
    }

    @Override
    public void visit(TermCons node) {
        if (!node.getCons().equals(MetaK.Constants.freshCons)) {
            super.visit(node);
            return;
        }
        if (!inCondition) {
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.COMPILER,
                    "Fresh can only be used in conditions.",
                    getName(), node.getFilename(), node.getLocation()));
        }
        final Term term = node.getContents().get(0);
        if (!(term instanceof  Variable)) {
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.COMPILER,
                    "Fresh can only be applied to variables, but was applied to\n\t\t" + term,
                    getName(), term.getFilename(), term.getLocation()));
        }
        Variable v = (Variable) term;
        if (left.containsKey(v)) {
            for (Variable v1 : left.keySet()) {
                if (v1.equals(v)) {
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.COMPILER,
                            "Fresh variable \"" + v1 + "\" is bound in the rule pattern.",
                            getName(), v1.getFilename(), v1.getLocation()));
                }
            }
        }
        left.put(v, new Integer(1));
    }

    @Override
    public void visit(Sentence node) {
        inCondition = false;
        left.clear();
        right.clear();
        fresh.clear();
        current = left;
        node.getBody().accept(this);
        if (node.getRequires() != null) {
            current = right;
            inCondition = true;
            node.getRequires().accept(this);
        }
        //TODO: add checks for Ensures, too.
        for (Variable v : right.keySet()) {
            if (MetaK.isAnonVar(v) && !v.isFresh()) {
                GlobalSettings.kem.register(new KException(KException
                        .ExceptionType.ERROR,
                        KException.KExceptionGroup.COMPILER,
                        "Anonymous variable found in the right hand side of a rewrite.",
                        getName(), v.getFilename(), v.getLocation()));
            }
            if (!left.containsKey(v)) {
                node.addAttribute(UNBOUNDED_VARS, "");
                
                /* matching logic relaxes this restriction */
                if (!options.backend.java()) {
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.COMPILER,
                            "Unbounded Variable " + v.toString() + ".",
                            getName(), v.getFilename(), v.getLocation()));
                } else {
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING,
                            KException.KExceptionGroup.COMPILER,
                            "Unbounded Variable " + v.toString() + ".",
                            getName(), v.getFilename(), v.getLocation()));
                }
            }
        }
        for (Map.Entry<Variable,Integer> e : left.entrySet()) {
            final Variable key = e.getKey();
            if (fresh.containsKey(key)) {
                GlobalSettings.kem.register(new KException(KException
                        .ExceptionType.ERROR,
                        KException.KExceptionGroup.COMPILER,
                        "Variable " + key + " has the same name as a fresh " +
                                "variable.",
                        getName(), key.getFilename(), key.getLocation()));
            }
            if (MetaK.isAnonVar(key)) continue;
            if (e.getValue().intValue()>1) continue;
            if (!right.containsKey(key)) {
                GlobalSettings.kem.register(new KException(KException.ExceptionType.HIDDENWARNING,
                        KException.KExceptionGroup.COMPILER,
                        "Singleton variable " + key.toString() + ".\n" +
                                "    If this is not a spelling mistake, please consider using anonymous variables.",
                        getName(), key.getFilename(), key.getLocation()));
            }
        }
    }
}
