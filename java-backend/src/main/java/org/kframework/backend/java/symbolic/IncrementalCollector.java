// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.function.BiConsumer;
import java.util.function.Function;

import org.kframework.backend.java.kil.JavaSymbolicObject;


/**
 * A visitor which computes the a set of results in a term based
 * on a specified criteria.
 *
 * @author AndreiS
 */
public class IncrementalCollector<T> extends PrePostVisitor {

    private Set<T> set = new HashSet<>();
    private final Stack<Set<T>> setStack = new Stack<>();
    private final BiConsumer<Set<T>, JavaSymbolicObject> setValue;
    private final Function<JavaSymbolicObject, Set<T>> getValue;
    private final Map<JavaSymbolicObject, Set<T>> intermediate;

    public IncrementalCollector(
            BiConsumer<Set<T>, JavaSymbolicObject> setValue,
            Function<JavaSymbolicObject, Set<T>> getValue,
            Map<JavaSymbolicObject, Set<T>> intermediate,
            LocalVisitor computeLocal) {
        getPreVisitor().addVisitor(new PreIncrementalVisitor());
        getPostVisitor().addVisitor(computeLocal);
        getPostVisitor().addVisitor(new PostIncrementalVisitor());
        this.setValue = setValue;
        this.intermediate = intermediate;
        this.getValue = getValue;
    }

    private class PreIncrementalVisitor extends LocalVisitor {
        @Override
        public void visit(JavaSymbolicObject term) {
            Set<T> termSet = getValue.apply(term);
            if (termSet == null) {
                termSet = intermediate.get(term);
            }
            if (termSet != null) {
                proceed = false;
                set.addAll(termSet);
            } else {
                setStack.push(set);
                set = new HashSet<>();
                intermediate.put(term, set);
            }
        }
    }

    private class PostIncrementalVisitor extends LocalVisitor {
        @Override
        public void visit(JavaSymbolicObject term) {
            set = setStack.pop();
            set.addAll(intermediate.get(term));
            setValue.accept(intermediate.get(term), term);
            intermediate.remove(term);
        }
    }

    /**
     * Gets the computed set of values in the term which accepts this
     * visitor.
     *
     * @return the set of result values in that term
     */
    public Set<T> getResultSet() {
        return set;
    }

}
