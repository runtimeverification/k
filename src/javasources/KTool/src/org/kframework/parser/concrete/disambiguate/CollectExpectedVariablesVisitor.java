// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
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
    public Set<Multimap<String, String>> vars = new HashSet<>();

    @Override
    public Void visit(Ambiguity node, Void _) {
        Set<Multimap<String, String>> newVars = new HashSet<>();
        for (Term t : node.getContents()) {
            CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(context);
            viz.visitNode(t);
            // create the split
            for (Multimap<String, String> elem : vars) { // for every local type restrictions
                for (Multimap<String, String> elem2 : viz.vars) { // create a combination with every ambiguity detected
                    Multimap<String, String> clone = HashMultimap.create();
                    clone.putAll(elem);
                    clone.putAll(elem2);
                    newVars.add(clone);
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
                vars.add(HashMultimap.<String, String>create());
            for (Multimap<String, String> vars2 : vars)
                vars2.put(var.getName(), var.getExpectedSort().getName());
        }
        return null;
    }
}
