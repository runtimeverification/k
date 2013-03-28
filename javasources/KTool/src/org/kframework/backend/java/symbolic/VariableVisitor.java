package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Set;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:39 AM
 * To change this template use File | Settings | File Templates.
 */
public class VariableVisitor extends AbstractVisitor {

    private final Set<Variable> variableSet = new HashSet<Variable>();

    public Set<Variable> getVariableSet() {
        return variableSet;
    }

    @Override
    public void visit(Variable variable) {
        variableSet.add(variable);
    }

}
