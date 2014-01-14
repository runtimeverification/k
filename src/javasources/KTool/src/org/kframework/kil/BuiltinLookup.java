package org.kframework.kil;

import java.util.ArrayList;

/**
 * Abstract class for Builtin Lookups
 *
 * @author TraianSF
 */
public abstract class BuiltinLookup extends Term {
    /** {@link Term} representation of a key */
    private final Term key;

    /** {@link Variable} representing the set */
    private final Variable base;

    /** {@link KSorts} representation of the the kind of the value returned by this lookup */
    private final KSort kind;

    protected BuiltinLookup(Variable base, Term key, KSort kind) {

        this.base = base;
        this.key = key;
        this.kind = kind;
    }

    public Variable base() {
        return base;
    }

    public Term key() {
        return key;
    }

    public KSort kind() {
        return kind;
    }

    public abstract Term value();
    
}
