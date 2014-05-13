// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Variable;


/**
 * A visitor which computes the set of variables in a term.
 * 
 * @author AndreiS
 */
public class VariableCollector extends PrePostVisitor {

    private Set<Variable> variableSet = new HashSet<Variable>();
    private final Stack<Set<Variable>> variableSetStack = new Stack<Set<Variable>>();

    public VariableCollector() {
        getPreVisitor().addVisitor(new PreVariableVisitor());
        getPostVisitor().addVisitor(new LocalVariableVisitor());
        getPostVisitor().addVisitor(new PostVariableVisitor());
    }

    private class PreVariableVisitor extends LocalVisitor {
        @Override
        public void visit(JavaSymbolicObject term) {
            Set<Variable> termVariableSet = term.getVariableSet();
            if (termVariableSet != null) {
                proceed = false;
                variableSet.addAll(termVariableSet);
            } else {
                variableSetStack.push(variableSet);
                variableSet = new HashSet<Variable>();
            }
        }
    }

    private class PostVariableVisitor extends LocalVisitor {
        @Override
        public void visit(JavaSymbolicObject term) {
            term.setVariableSet(variableSet);
            variableSet = variableSetStack.pop();
            variableSet.addAll(term.getVariableSet());
        }
    }

    private class LocalVariableVisitor extends LocalVisitor {
        @Override
        public void visit(Variable variable) {
            variableSet.add(variable);
        }
    }

    /**
     * Gets the computed set of variables in the term which accepts this
     * visitor.
     * 
     * @return the set of variables in that term
     */
    public Set<Variable> getVariableSet() {
        return variableSet;
    }

}
