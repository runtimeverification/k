// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * A variable which represents a concrete collection.
 *
 * @author AndreiS
 */
public class ConcreteCollectionVariable extends Variable {

    private final int concreteSize;

    public ConcreteCollectionVariable(String name, Sort sort, boolean anonymous, int concreteSize) {
        super(name, sort, anonymous, -1);
        this.concreteSize = concreteSize;
    }

    public ConcreteCollectionVariable(String name, Sort sort, int concreteSize) {
        this(name, sort, false, concreteSize);
    }

    public int concreteCollectionSize() {
        return concreteSize;
    }

    public boolean match(Term term) {
        if (term instanceof ConcreteCollectionVariable) {
            return concreteCollectionSize() == ((ConcreteCollectionVariable) term).concreteCollectionSize();
        } else if (term instanceof Collection) {
            Collection collection = (Collection) term;
            return collection.isConcreteCollection() && collection.concreteSize() == concreteSize;
        } else {
            return false;
        }
    }

    public boolean unify(Term term) {
        if (term instanceof ConcreteCollectionVariable) {
            return concreteCollectionSize() == ((ConcreteCollectionVariable) term).concreteCollectionSize();
        } else if (term instanceof Collection) {
            Collection collection = (Collection) term;
            return collection.isConcreteCollection() ?
                collection.concreteSize() == concreteSize :
                collection.concreteSize() <= concreteSize;
        } else if (term instanceof Variable) {
            return true;
        } else {
            return false;
        }
    }

    @Override
    public ConcreteCollectionVariable getFreshCopy() {
        ConcreteCollectionVariable var = new ConcreteCollectionVariable(
                Variable.getAnonVariable(sort()).name(),
                sort(),
                true,
                concreteSize);
        var.copyAttributesFrom(this);
        return var;
    }

}
