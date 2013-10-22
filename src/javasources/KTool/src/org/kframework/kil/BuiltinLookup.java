package org.kframework.kil;

/**
 * Abstract class for Builtin Lookups
 *
 * @author TraianSF
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

    public abstract Term value();
}
