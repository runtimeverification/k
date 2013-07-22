package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;


/**
 * @author: AndreiS
 */
public class BuiltinSet extends Collection {

    public abstract class Operation {

        private final Term element;

        protected Operation(Term element) {
            this.element = element;
        }

        public Term element() {
            return element;
        }

    }

    public class Insertion extends Operation {

        private Insertion(Term element) {
            super(element);
        }

    }

    public class Deletion extends Operation {

        private Deletion(Term element) {
            super(element);
        }

    }

    private final Set<Term> elements;
    private final Queue<Operation> operations;

    public BuiltinSet(Set<Term> elements) {
        this(elements, null);
    }

    public BuiltinSet(Set<Term> elements, Variable frame) {
        super(frame, Kind.KITEM);
        this.elements = new HashSet<Term>(elements);
        operations = new ArrayDeque<Operation>();
    }


    public boolean contains(Term key) {
        return elements.contains(key);
    }

    public void add(Term element) {
        if (!(operations.isEmpty() && elements.contains(element))) {
            operations.add(new Insertion(element));
        }
    }

    public Set<Term> elements() {
        return Collections.unmodifiableSet(elements);
    }

    public Queue<Operation> operations() {
        return operations;
    }

    public void remove(Term element) {
        if (!(operations.isEmpty() && elements.contains(element))) {
            operations.add(new Deletion(element));
        } else {
            elements.remove(element);
        }
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
        return super.equals(set) && elements.equals(set.elements)
               && operations.equals(set.operations);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + (super.frame == null ? 0 : super.frame.hashCode());
        hash = hash * Utils.HASH_PRIME + elements.hashCode();
        hash = hash * Utils.HASH_PRIME + operations.hashCode();
        return hash;
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}
