// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A HashMap-backed {@link Substitution}. Surprisingly, it is faster than {@link ArraySubstitution} for non-trivial
 * definitions.
 */
public class HashMapSubstitution extends HashMap<Variable, Term> implements Substitution<Variable, Term> {

    @Override
    public HashMapSubstitution plus(Variable key, Term value) {
        Term previousValue = get(key.ordinal());
        if (previousValue == null) {
            super.put(key, value);
            return this;
        } else if (previousValue.equals(value)) {
            return this;
        } else {
            return null;
        }
    }

    @Override
    public Substitution<Variable, Term> minus(Variable key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Substitution<Variable, Term> minusAll(Collection<? extends Variable> keys) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Substitution<Variable, Term> evaluate(TermContext context) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<Equality> equalities(GlobalContext global) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isFalse(GlobalContext global) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term put(Variable key, Term value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term remove(Object key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void putAll(Map<? extends Variable, ? extends Term> m) {
        throw new UnsupportedOperationException();
    }
}
