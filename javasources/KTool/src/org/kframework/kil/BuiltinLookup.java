package org.kframework.kil;

/**
 * Created with IntelliJ IDEA.
 * User: Traian
 * Date: 03.07.2013
 * Time: 21:29
 * To change this template use File | Settings | File Templates.
 */
public abstract class BuiltinLookup extends Term {
    /** {@link org.kframework.kil.Term} representation of a key */
    private final Term key;

    /** {@link org.kframework.kil.Variable} representing the set */
    private final Variable base;

    protected BuiltinLookup(Variable base, Term key) {
        this.base = base;
        this.key = key;
    }

    public Variable base() {
        return base;
    }

    public Term key() {
        return key;
    }
}
