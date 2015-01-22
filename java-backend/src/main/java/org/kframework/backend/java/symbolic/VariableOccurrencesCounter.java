// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

/**
 * Counts the occurrences of all variables inside a {@link Term}.
 *
 * @author YilongL
 *
 */
public class VariableOccurrencesCounter extends BottomUpVisitor {

    private final Multiset<Variable> variables = HashMultiset.create();

    private VariableOccurrencesCounter() { }

    @Override
    public void visit(Variable variable) {
        variables.add(variable);
    }

    public static Multiset<Variable> count(Term term) {
        VariableOccurrencesCounter counter = new VariableOccurrencesCounter();
        term.accept(counter);
        return counter.variables;
    }
}
