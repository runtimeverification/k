package org.kframework.kil.visitors;

public interface Visitable {
    /**
     * Implements a Visitor pattern.
     * @param visitor
     */
    public <P, R> R accept(Visitor<P, R> visitor, P p);
    
    /**
     * Implements a visitor pattern with no parameters
     * @param visitor
     * @return
     */
    public <R> R accept(Visitor<Void, R> visitor);
}
