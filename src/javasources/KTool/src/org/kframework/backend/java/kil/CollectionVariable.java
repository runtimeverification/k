package org.kframework.backend.java.kil;

/**
 * @author AndreiS
 */
public class CollectionVariable extends Variable {

    private final int concreteSize;

    public CollectionVariable(String name, String sort, boolean anonymous, int concreteSize) {
        super(name, sort, anonymous);
        this.concreteSize = concreteSize;
    }

    public CollectionVariable(String name, String sort, int concreteSize) {
        this(name, sort, false, concreteSize);
    }

    public int concreteCollectionSize() {
        return concreteSize;
    }

    @Override
    public CollectionVariable getFreshCopy() {
        return new CollectionVariable(
                Variable.getFreshVariable(sort()).name(),
                sort(),
                true,
                concreteSize);
    }

}
