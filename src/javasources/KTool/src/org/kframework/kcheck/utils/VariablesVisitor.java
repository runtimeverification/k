// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class VariablesVisitor extends BasicVisitor {

    List<Variable> variables;
    
    public VariablesVisitor(Context context) {
        super(context);
        variables = new ArrayList<Variable>();
    }

    @Override
    public Void visit(Variable node, Void _) {
        variables.add(node);
        return super.visit(node, _);
    }
    
    public List<Variable> getVariables() {
        return variables;
    }
}
