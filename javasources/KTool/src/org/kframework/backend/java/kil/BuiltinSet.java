package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
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
        super(null, Kind.KITEM);
        this.elements = new HashSet<Term>(elements);
        operations = new ArrayDeque<Operation>();
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
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
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
