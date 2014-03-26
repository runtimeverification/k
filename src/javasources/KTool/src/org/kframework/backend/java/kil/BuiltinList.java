package org.kframework.backend.java.kil;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.ImprovedArrayDeque;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.base.Joiner;


/**
 * @author: TraianSF
 */
public class BuiltinList extends Collection {

    private final ImprovedArrayDeque<Term> elementsLeft;
    protected final ImprovedArrayDeque<Term> elementsRight;
    protected final int removeLeft;
    protected final int removeRight;
//    private final Queue<Operation> operations;

    public BuiltinList(java.util.Collection<Term> elements) {
        this(null, 0, 0, elements, Collections.<Term>emptyList());
    }

    public BuiltinList(Variable frame, int removeLeft, int removeRight, java.util.Collection<Term> elementsLeft, java.util.Collection<Term> elementsRight) {
        super(frame, Kind.KITEM);
        this.elementsLeft = new ImprovedArrayDeque<Term>(elementsLeft);
        if (frame == null) {
            assert removeLeft == 0 && removeRight == 0 : "cannot remove from an empty base";
            this.elementsLeft.addAll(elementsRight);
            this.elementsRight = new ImprovedArrayDeque<Term>();
        } else {
            this.elementsRight = new ImprovedArrayDeque<Term>(elementsRight);
        }
        this.removeLeft = removeLeft;
        this.removeRight = removeRight;
    }

    public BuiltinList(Variable frame) {
        this(frame, 0, 0, Collections.<Term>emptyList(), Collections.<Term>emptyList());
    }

    public BuiltinList() {
        this(null, 0, 0, Collections.<Term>emptyList(), Collections.<Term>emptyList());
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
    public int size() {
        return elementsLeft.size() + elementsRight.size();
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public String sort() {
        return KSorts.LIST;
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
        return (frame == null ? list.frame == null : frame.equals(list.frame))
                && removeLeft == list.removeLeft
                && removeRight == list.removeRight
                && elementsLeft.equals(list.elementsLeft)
                && elementsRight.equals(list.elementsRight);
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
            hashCode = hashCode * Utils.HASH_PRIME + removeLeft;
            hashCode = hashCode * Utils.HASH_PRIME + removeRight;
            hashCode = hashCode * Utils.HASH_PRIME + elementsLeft.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + elementsRight.hashCode();
        }
        return hashCode;
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

    public Term get(int index) {
        boolean onLeft = true;
        Deque<Term> elements = elementsLeft;
        Iterator<Term> iterator = elements.iterator();
        if (frame == null) { // no framing variable
            if (!elementsRight.isEmpty()) {
                elementsLeft.addAll(elementsRight); // move all elements to the left
                elementsRight.clear();
            }
        } else { // if there is a frame
            if (index < 0) { // search among the elements on the right of frame if index < 0
                onLeft = false;
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
        // TODO(AndreiS): use correct kind/sort
        if (frame == null) return new Bottom(Kind.K);
        java.util.Collection<Term> left = elementsLeft;
        java.util.Collection<Term> right = elementsRight;
        if (onLeft) {
            index -= elementsLeft.size();
            left = Collections.<Term>emptyList();
        } else {
            index -= elementsRight.size();
            index = -index-1;
            right = Collections.<Term>emptyList();
        }

        // TODO(AndreiS): use correct kind/sort
        return new ListLookup(
                BuiltinList.of(frame, removeLeft, removeRight, left, right),
                IntToken.of(index),
                Kind.K);
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
            if (removeLeft != 0 || removeRight != 0) {
                stringBuilder.append("remove(" + removeLeft + ", ");
            }
            stringBuilder.append(super.frame);
            if (removeLeft != 0 || removeRight != 0) {
                stringBuilder.append(", " + removeRight + ")");
            }
        }
        joiner.appendTo(stringBuilder, elementsRight);
        if (stringBuilder.length() == 0) {
            stringBuilder.append(identity);
        }
        return stringBuilder.toString();
    }

    public static BuiltinList of(Term frame, int removeLeft, int removeRight, java.util.Collection<Term> elementsLeft, java.util.Collection<Term> elementsRight) {
        if (frame instanceof BuiltinList) {
            BuiltinList builtinList = (BuiltinList) frame;
            if (!builtinList.hasFrame()) {
                assert builtinList.elementsRight.isEmpty();
                assert builtinList.elementsLeft().size() >= removeLeft + removeRight;
                if (builtinList.elementsLeft().size() > removeLeft + removeRight) {
                    Iterator<Term> iterator = builtinList.elementsLeft.iterator();
                    int deleted = removeLeft + removeRight;
                    while (removeLeft > 0) {
                        removeLeft--; iterator.next();
                    }
                    for (int i = deleted; i < builtinList.elementsLeft.size(); i++) {
                        elementsLeft.add(iterator.next());
                    }
                }
                frame = null; removeLeft = 0; removeRight = 0;
            } else {
                Iterator<Term> iterator = builtinList.elementsLeft().iterator();
                while (removeLeft > 0 && iterator.hasNext()) {
                    removeLeft--; iterator.next();
                }
                while (iterator.hasNext()) {
                    elementsLeft.add(iterator.next());
                }
                removeLeft += builtinList.removeLeft;

                ArrayList<Term> right = new ArrayList<Term>();
                iterator = builtinList.elementsRight.iterator();
                int size = builtinList.elementsRight.size();
                for (int i = removeRight; i < size; i++) {
                   right.add(iterator.next());
                }
                right.addAll(elementsRight);
                if (removeRight > size) {
                    removeRight -= size;
                } else removeRight = 0;
                removeRight += builtinList.removeRight;
                right.addAll(elementsRight);
                return new BuiltinList(builtinList.frame, removeLeft, removeRight, elementsLeft, right);
            }
        }
        if (frame == null) {
            assert removeLeft == 0 && removeRight == 0 : "cannot remove from an empty list";
            elementsLeft.addAll(elementsRight);
            return new BuiltinList(null, 0, 0, elementsLeft, Collections.<Term>emptyList());
        }
        if (frame instanceof Variable)
            return new BuiltinList((Variable) frame, removeLeft, removeRight, elementsLeft, elementsRight);

        assert false : "Frame can only be substituted by a Variable or a BuiltinList, or deleted.";
        return null;
    }

    public int removeLeft() {
        return removeLeft;
    }

    public int removeRight() {
        return removeRight;
    }

}
