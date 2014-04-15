// Copyright (C) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

/**
 * Builtin set lookup operation. The operation has the form {@code truth := set[key]} with
 * the semantics that {@code set} contains an entry matching {@code key}. When
 * resolving a lookup operation during the application a rule, the variables in {@code key} must
 * be already bound, while the variables in {@code truth} may be bound by this lookup  operation.
 *
 * @author TraianSF  (refactoring from {@link org.kframework.kil.MapLookup})
 */
public class SetLookup extends BuiltinLookup {

    public SetLookup(Variable base, Term key, boolean choice) {
        super(base, key, KSort.KItem, choice);
    }

    @Override
    public Term value() {
        return BoolBuiltin.TRUE;
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + base().hashCode();
        hash = hash * Context.HASH_PRIME + key().hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof SetLookup)) {
            return false;
        }

        SetLookup mapLookup = (SetLookup) object;
        return base().equals(mapLookup.base()) && key().equals(mapLookup.key());
    }
    
    @Override
    public <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.visit(this, p);
    }
}
