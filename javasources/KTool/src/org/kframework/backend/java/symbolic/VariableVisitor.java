package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:39 AM
 * To change this template use File | Settings | File Templates.
 */
public class VariableVisitor extends PrePostVisitor {

    private Set<Variable> variableSet = new HashSet<Variable>();
    private final Stack<Set<Variable>> variableSetStack = new Stack<Set<Variable>>();

    public VariableVisitor() {
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

    public Set<Variable> getVariableSet() {
        return variableSet;
    }

}
