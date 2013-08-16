package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.*;
import java.util.Collection;

/**
 *
 * @author TraianSF
 */
public class ListUpdate {

    /** {@code Set} of keys to be removed from the map */
//    private int removeLeft;
//    private int removeRight;
//
//    public ListUpdate(Variable list,  int removeLeft, int removeRight, Collection<Term> addLeft, Collection<Term> addRight) {
//        super(list, 0, 0, addLeft,addRight);
//        this.removeLeft = removeLeft;
//        this.removeRight = removeRight;
//    }
//
//    public Term evaluateUpdate() {
//        if (removeLeft == 0 && removeRight == 0) {
//            if (elementsLeft().isEmpty() && elementsRight().isEmpty()) return frame();
//            return BuiltinList.of(frame(), 0, 0, elementsLeft(), elementsRight());
//        }
//
//        if (!(frame instanceof BuiltinList)) {
//            return this;
//        }
//
//        BuiltinList builtinList = ((BuiltinList) frame);
//
//        ArrayDeque<Term> elementsLeft = new ArrayDeque<Term>(builtinList.elementsLeft());
//        for (Iterator<Term> iterator = elementsLeft.iterator(); removeLeft > 0 && iterator.hasNext();) {
//            removeLeft--;
//            iterator.next(); iterator.remove();
//        }
//
//        ArrayDeque<Term> elementsRight = new ArrayDeque<Term>(builtinList.elementsRight());
//        for (Iterator<Term> iterator = elementsRight.descendingIterator(); removeRight > 0 && iterator.hasNext();) {
//            removeRight--;
//            iterator.next(); iterator.remove();
//        }
//
//        if (removeLeft > 0 && removeRight > 0) {
//            return new ListUpdate(builtinList, removeLeft, removeRight);
//        }
//
//        if (builtinList.hasFrame()) {
//            return new BuiltinList(builtinList.frame(), 0, 0, elementsLeft, elementsRight);
//        } else {
//            elementsLeft.addAll(elementsRight);
//            return new BuiltinList(elementsLeft);
//        }
//    }
//
//    public Term base() {
//        return frame;
//    }
//
//    public int removeLeft() {
//        return removeLeft;
//    }
//
//    public int removeRight() {
//        return removeRight;
//    }
//
//    @Override
//    public boolean isSymbolic() {
//        throw new UnsupportedOperationException();
//    }
//
//    @Override
//    public int hashCode() {
//        int hash = 1;
//        hash = hash * Utils.HASH_PRIME + frame.hashCode();
//        hash = hash * Utils.HASH_PRIME + removeLeft;
//        hash = hash * Utils.HASH_PRIME + removeRight;
//        return hash;
//    }
//
//    @Override
//    public boolean equals(Object object) {
//        if (this == object) {
//            return true;
//        }
//
//        if (!(object instanceof ListUpdate)) {
//            return false;
//        }
//
//        ListUpdate mapUpdate = (ListUpdate) object;
//        return frame.equals(mapUpdate.frame)
//                && removeLeft == mapUpdate.removeLeft
//                && removeRight == mapUpdate.removeRight;
//    }
//
//    @Override
//    public String toString() {
//        String s = frame.toString();
//        for (int r = removeLeft; r > 0; r--) {
//            s = "removeFirst(" + s + ")";
//        }
//        for (int r = removeRight; r > 0; r--) {
//            s = "removeLast(" + s + ")";
//        }
//        return s;
//    }
//
//    @Override
//    public void accept(Unifier unifier, Term patten) {
//        throw new UnsupportedOperationException();
//    }
//
//    @Override
//    public ASTNode accept(Transformer transformer) {
//        return transformer.transform(this);
//    }
//
//    @Override
//    public void accept(Visitor visitor) {
//        visitor.visit(this);
//    }
//
}
