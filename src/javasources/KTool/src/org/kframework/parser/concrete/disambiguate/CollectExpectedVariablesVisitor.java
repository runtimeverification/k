// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.*;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectExpectedVariablesVisitor extends BasicVisitor {
    public CollectExpectedVariablesVisitor(Context context) {
        super(context);
    }

    /**
     * Each element in the list is a Mapping from variable name and a list of constraints for that variable.
     * On each Ambiguity node, a cartesian product is created between the current List and each ambiguity variant.
     */
    public Set<VarHashMap> vars = new HashSet<>();

    @Override
    public Void visit(Ambiguity node, Void _) {
        Set<VarHashMap> newVars = new HashSet<>();
        for (Term t : node.getContents()) {
            CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(context);
            viz.visitNode(t);
            // create the split
            for (VarHashMap elem : vars) { // for every local type restrictions
                for (VarHashMap elem2 : viz.vars) { // create a combination with every ambiguity detected
                    newVars.add(elem.deepClone().addAll(elem2));
                }
            }
            if (vars.size() == 0)
                newVars.addAll(viz.vars);
        }
        if (!newVars.isEmpty())
            vars = newVars;
        return visit((Term) node, _);
    }

    @Override
    public Void visit(Variable var, Void _) {
        if (!var.isUserTyped() && !var.getName().equals(MetaK.Constants.anyVarSymbol)) {
            if (vars.isEmpty())
                vars.add(new VarHashMap());
            for (VarHashMap vars2 : vars)
                if (vars2.containsKey(var.getName())) {
                    vars2.get(var.getName()).add(var.getExpectedSort());
                } else {
                    java.util.Set<String> varss = new HashSet<>();
                    varss.add(var.getExpectedSort());
                    vars2.put(var.getName(), varss);
                }
        }
        return null;
    }
}
