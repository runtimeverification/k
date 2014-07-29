// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;


/**
 * Class representing a set. It only has one frame (which is a variable), and concrete elements.
 * A set composed of multiple set variables or terms (in addition to the elements) is represented
 * using concatenation (and can only occur in the right-hand side or in the condition).
 *
 * @author AndreiS
 */
public class BuiltinSet extends Collection {

//    public abstract class Operation {
//
//        private final Term element;
//
//        protected Operation(Term element) {
//            this.element = element;
//        }
//
//        public Term element() {
//            return element;
//        }
//
//    }
//
//    public class Insertion extends Operation {
//
//        private Insertion(Term element) {
//            super(element);
//        }
//
//    }
//
//    public class Deletion extends Operation {
//
//        private Deletion(Term element) {
//            super(element);
//        }
//
//    }

    private final Set<Term> elements;
//    private final Queue<Operation> operations;

    public BuiltinSet(Set<? extends Term> elements) {
        this(elements, null);
    }

    public BuiltinSet(Set<? extends Term> elements, Variable frame) {
        super(frame, Kind.KITEM);
        this.elements = new HashSet<Term>(elements);
//        operations = new ArrayDeque<Operation>();
    }

    public BuiltinSet(Variable frame) {
        super(frame, Kind.KITEM);
        this.elements = new HashSet<Term>();
//        operations = new ArrayDeque<Operation>();
    }

    public BuiltinSet() {
        super(null, Kind.KITEM);
        elements = new HashSet<Term>();
//        operations = new ArrayDeque<Operation>();
    }

    public boolean contains(Term key) {
        return elements.contains(key);
    }

    public void add(Term element) {
        elements.add(element);
//        if (!(operations.isEmpty() && elements.contains(element))) {
//            operations.add(new Insertion(element));
//        }
    }

    public Set<Term> elements() {
        return Collections.unmodifiableSet(elements);
    }

//    public Queue<Operation> operations() {
//        return operations;
//    }

//    public void remove(Term element) {
//        if (!(operations.isEmpty() && elements.contains(element))) {
//            operations.add(new Deletion(element));
//        } else {
//            elements.remove(element);
//        }
//    }

    @Override
    public int size() {
        return elements.size();
    }

    /**
     * {@code BuiltinSet} is guaranteed to have only one frame; thus, they can
     * always be used in the left-hand side of a rule.
     */
    @Override
    public boolean isLHSView() {
        // TODO(YilongL): allow BuiltinSet to have a list of Terms instead of
        // just substitution entries; revise the javadoc
        return true;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.SET;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinSet)) {
            return false;
        }

        BuiltinSet set = (BuiltinSet) object;
        return (frame == null ? set.frame == null : frame.equals(set.frame))
                && elements.equals(set.elements);
        //               && operations.equals(set.operations);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
        hashCode = hashCode * Utils.HASH_PRIME + elements.hashCode();
        // hashCode = hashCode * Utils.HASH_PRIME + operations.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeHasCell() {
        boolean hasCell = false;
        for (Term term : elements) {
            hasCell = hasCell || term.hasCell();
            if (hasCell) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }


    @Override
    public String toString() {
        return toString(" ", ".Set");
    }

    public String toString(String operator, String identity) {
        Joiner joiner = Joiner.on(operator);
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, elements);
        if (super.frame != null) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(operator);
            }
            stringBuilder.append(super.frame);
        }
        if (stringBuilder.length() == 0) {
            stringBuilder.append(identity);
        }
        return stringBuilder.toString();
    }

    public static BuiltinSet of(Set<Term> elements, Term frame) {
        if (frame == null) {
            return new BuiltinSet(elements);
        }
        if (frame instanceof Variable)
            return new BuiltinSet(elements, (Variable) frame);
        if (frame instanceof BuiltinSet) {
            BuiltinSet builtinSet = (BuiltinSet) frame;
            builtinSet = new BuiltinSet(builtinSet.elements, builtinSet.frame);
            builtinSet.elements.addAll(elements);
            return builtinSet;
        }
        assert false : "Frame can only be substituted by a Variable or a BuiltinSet, or deleted.";
        return null;
    }

}
