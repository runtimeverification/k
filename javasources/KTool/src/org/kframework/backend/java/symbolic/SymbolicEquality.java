package org.kframework.backend.java.symbolic;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 11:28 AM
 * To change this template use File | Settings | File Templates.
 */
public class SymbolicEquality {

    public final Term lhs, rhs;

    SymbolicEquality(Term lhs, Term rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    @Override
    public String toString() {
        return lhs + " =? " + rhs;
    }

}
