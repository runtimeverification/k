// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

public interface Visitable {
    /**
     * Implements a Visitor pattern.
     * @param visitor
     */
    public <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E;
    
    /**
     * Implements a visitor pattern with no parameters
     * @param visitor
     * @return
     */
    public <R, E extends Throwable> R accept(Visitor<Void, R, E> visitor) throws E;
}
