package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.*;


/**
 * @author: TraianSF
 */
public class BuiltinList extends Collection {

    private final ArrayDeque<Term> elementsLeft;
    private final ArrayDeque<Term> elementsRight;
//    private final Queue<Operation> operations;

    public BuiltinList(java.util.Collection<Term> elements) {
        this(elements, Collections.<Term>emptyList(), null);
    }

    public BuiltinList(java.util.Collection<Term> elementsLeft, java.util.Collection<Term> elementsRight, Variable frame) {
        super(frame, Kind.KITEM);
        this.elementsLeft = new ArrayDeque<Term>(elementsLeft);
        if (frame == null) {
            this.elementsLeft.addAll(elementsRight);
            this.elementsRight = new ArrayDeque<Term>();
        } else {
            this.elementsRight = new ArrayDeque<Term>(elementsRight);
        }
    }

    public BuiltinList(Variable frame) {
        this(Collections.<Term>emptyList(), Collections.<Term>emptyList(), frame);
    }

    public BuiltinList() {
        this(Collections.<Term>emptyList(), Collections.<Term>emptyList(), null);
    }

    public boolean contains(Term key) {
        return elementsLeft.contains(key) || elementsRight.contains(key);
    }

    public void add(Term element) {
        addRight(element);
    }

    public void addRight(Term element) {
        elementsRight.add(element);
    }

    public void addLeft(Term element) {
        elementsLeft.addFirst(element);
    }

    public List<Term> elements() {
        ArrayList<Term> elements = new ArrayList<Term>(elementsLeft);
        elements.addAll(elementsRight);
        return Collections.unmodifiableList(elements);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinList)) {
            return false;
        }

        BuiltinList list = (BuiltinList) object;
        return super.equals(list) && elementsLeft.equals(list.elementsLeft) && elementsRight.equals(list.elementsRight);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + (super.frame == null ? 0 : super.frame.hashCode());
        hash = hash * Utils.HASH_PRIME + elementsLeft.hashCode();
        hash = hash * Utils.HASH_PRIME + elementsRight.hashCode();
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

    public Term get(int index) {
        Deque<Term> elements = elementsLeft;
        Iterator<Term> iterator = elements.iterator();
        if (frame == null) { // no framing variable
            if (!elementsRight.isEmpty()) {
                elementsLeft.addAll(elementsRight); // move all elements to the left
                elementsRight.clear();
            }
        } else { // if there is a frame
            if (index < 0) { // search among the elements on the right of frame if index < 0
                elements = elementsRight;
            }
        }
        if (index < 0) { // search from the end if index < 0
            iterator = elements.descendingIterator();
            index = -index-1; // index from the end
        }
        if (index < elements.size()) { // if there are enough elements
            while (index-- > 0) iterator.next();
            return iterator.next();
        }
        return null;
    }

    public java.util.Collection<Term> elementsLeft() {
        return Collections.unmodifiableCollection(elementsLeft);
    }

    public java.util.Collection<Term> elementsRight() {
        return Collections.unmodifiableCollection(elementsRight);
    }

    @Override
    public String toString() {
        return toString(" ", ".List");
    }

    public String toString(String operator, String identity) {
        Joiner joiner = Joiner.on(operator);
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, elementsLeft);
        if (super.frame != null) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(operator);
            }
            stringBuilder.append(super.frame);
        }
        joiner.appendTo(stringBuilder, elementsRight);
        if (stringBuilder.length() == 0) {
            stringBuilder.append(identity);
        }
        return stringBuilder.toString();
    }
}
