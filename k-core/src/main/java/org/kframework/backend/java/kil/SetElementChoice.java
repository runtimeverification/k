// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 * Term representation of the operation of choosing an element from a set.
 *
 * @see org.kframework.backend.java.kil.BuiltinSet
 *
 * @author AndreiS
 */
public class SetElementChoice extends Term implements DataStructureChoice {

    /**
     * Set from which the element is chosen.
     */
    private final Term set;

    public SetElementChoice(Term set) {
        super(Kind.KITEM);
        this.set = set;
    }

    /**
     * Returns a non-deterministically chosen element from the set.
     * @return
     *     {@link org.kframework.backend.java.kil.Term} representation of an element if the set has elements
     *     {@link org.kframework.backend.java.kil.Bottom} is the set is empty (no elements and no frame)
     *     this object otherwise
     */
    public Term evaluateChoice() {
        if (!(set instanceof BuiltinSet)) {
            return this;
        }

        if (!((BuiltinSet) set).elements().isEmpty()) {
            return ((BuiltinSet) set).elements().iterator().next();
        } else if (((BuiltinSet) set).isEmpty()) {
            return Bottom.of(kind);
        } else {
            return this;
        }
    }

    public Term set() {
        return base();
    }

    @Override
    public Term base() {
        return set;
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return kind.asSort();
    }

    @Override
    public Type type() {
        return Type.SET_ELEMENT_CHOICE;
    }

    @Override
    protected int computeHash() {
        return set.hashCode();
    }

    @Override
    protected boolean computeMutability() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof SetElementChoice)) {
            return false;
        }

        SetElementChoice setElementChoice = (SetElementChoice) object;
        return set.equals(setElementChoice.set);
    }

    @Override
    public String toString() {
        return "choice(" + set.toString() + ")";
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
