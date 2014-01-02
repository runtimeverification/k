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

    @Override
    public ConcreteCollectionVariable getFreshCopy() {
        return new ConcreteCollectionVariable(
                Variable.getFreshVariable(sort()).name(),
                sort(),
                true,
                concreteSize);
    }

}
