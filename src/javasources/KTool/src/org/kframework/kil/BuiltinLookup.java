// Copyright (C) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

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

    /** True if the key of this lookup is not determined, and this lookup can choose one */
    private final boolean choice;

    protected BuiltinLookup(Variable base, Term key, KSort kind, boolean choice) {
        this.base = base;
        this.key = key;
        this.kind = kind;
        this.choice = choice;
    }

    public Variable base() {
        return base;
    }

    public boolean choice() {
        return choice;
    }

    public Term key() {
        return key;
    }

    public KSort kind() {
        return kind;
    }

    public abstract Term value();
    
}
