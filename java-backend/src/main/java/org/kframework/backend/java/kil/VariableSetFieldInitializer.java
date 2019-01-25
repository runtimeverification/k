// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BasicVisitor;

import org.pcollections.HashTreePSet;
import org.pcollections.PSet;


public class VariableSetFieldInitializer extends BasicVisitor {

    private PSet<Variable> variables = HashTreePSet.empty();

    @Override
    public void visitNode(JavaSymbolicObject node) {
        if (node.variableSet != null) {
            variables = variables.plusAll(node.variableSet);
            return;
        }

        PSet<Variable> parentVariables = variables;
        variables = HashTreePSet.empty();
        if (!(node instanceof KLabelConstant || node instanceof Token)) {
            super.visitNode(node);
        }
        node.variableSet = variables;
        variables = parentVariables.plusAll(variables);
    }

    @Override
    public void visit(Variable variable) {
        variables = variables.plus(variable);
    }

}
