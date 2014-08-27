// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * A variable which represents a concrete collection.
 *
 * @author AndreiS
 */
public class ConcreteCollectionVariable extends Variable {

    private final int concreteSize;

    public ConcreteCollectionVariable(String name, Sort sort, boolean anonymous, int concreteSize) {
        super(name, sort, anonymous);
        this.concreteSize = concreteSize;
    }

    public ConcreteCollectionVariable(String name, Sort sort, int concreteSize) {
        this(name, sort, false, concreteSize);
    }

    public int concreteCollectionSize() {
        return concreteSize;
    }

    public boolean matchConcreteSize(Term term) {
        if (term instanceof ConcreteCollectionVariable) {
            ConcreteCollectionVariable otherVariable = (ConcreteCollectionVariable) term;
            return concreteCollectionSize() == otherVariable.concreteCollectionSize();
        } else if (term instanceof Collection) {
            Collection collection = (Collection) term;
            if (!collection.isConcreteCollection()) {
                return collection.concreteSize() <= concreteSize;
            } else {
                return collection.concreteSize() == concreteSize;
            }
        } else {
            return false;
        }
    }

    @Override
    public ConcreteCollectionVariable getFreshCopy() {
        ConcreteCollectionVariable var = new ConcreteCollectionVariable(
                Variable.getFreshVariable(sort()).name(),
                sort(),
                true,
                concreteSize);
        var.copyAttributesFrom(this);
        return var;
    }

}
