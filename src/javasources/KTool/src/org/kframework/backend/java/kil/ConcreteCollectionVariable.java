// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

/**
 * A variable which represents a concrete collection.
 * 
 * @author AndreiS
 */
public class ConcreteCollectionVariable extends Variable {

    private final int concreteSize;

    public ConcreteCollectionVariable(String name, String sort, boolean anonymous, int concreteSize) {
        super(name, sort, anonymous);
        this.concreteSize = concreteSize;
    }

    public ConcreteCollectionVariable(String name, String sort, int concreteSize) {
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
            if (term instanceof BuiltinList && ((BuiltinList) term).isUpdate()) {
                return false;
            }
            
            Collection collection = (Collection) term;
            if (collection.hasFrame()) {
                return collection.size() <= concreteSize;
            } else {
                return collection.size() == concreteSize;
            }
        } else if (term instanceof Variable) {
            return true;
        } else {
            return false;
        }
    }

    @Override
    public ConcreteCollectionVariable getFreshCopy() {
        return new ConcreteCollectionVariable(
                Variable.getFreshVariable(sort()).name(),
                sort(),
                true,
                concreteSize);
    }

}
