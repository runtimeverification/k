// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:51 AM
 * To change this template use File | Settings | File Templates.
 */
public interface Visitable {
    /**
     * Implements a Visitor pattern.
     * @param visitor
     */
    void accept(Visitor visitor);
}
