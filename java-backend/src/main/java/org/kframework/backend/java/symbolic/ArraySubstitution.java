// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A mutable {@link Substitution} implementation backed by an array.
 */
public class ArraySubstitution implements Substitution<Variable, Term> {

    private final Term[] entries;
    private int size;

    public ArraySubstitution(int length) {
        entries = new Term[length];
        size = 0;
    }

    @Override
    public ArraySubstitution plus(Variable key, Term value) {
        Term previousValue = entries[key.ordinal()];
        if (previousValue == null) {
            entries[key.ordinal()] = value;
            size++;
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
    public int size() {
        return size;
    }

    @Override
    public boolean isEmpty() {
        return size == 0;
    }

    @Override
    public boolean containsKey(Object key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean containsValue(Object value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term get(Object key) {
        if (key instanceof Variable) {
            return entries[((Variable) key).ordinal()];
        } else {
            return null;
        }
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

    @Override
    public void clear() {
        Arrays.fill(entries, null);
        size = 0;
    }

    @Override
    public Set<Variable> keySet() {
        throw new UnsupportedOperationException("keySet");
    }

    @Override
    public Collection<Term> values() {
        throw new UnsupportedOperationException("values");
    }

    @Override
    public Set<Entry<Variable, Term>> entrySet() {
        throw new UnsupportedOperationException("entrySet");
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ArraySubstitution)) {
            return false;
        }

        ArraySubstitution substitution = (ArraySubstitution) object;
        return Arrays.equals(entries, substitution.entries);
    }

    @Override
    public int hashCode() {
        return Arrays.hashCode(entries);
    }

    @Override
    public String toString() {
        return Arrays.toString(entries);
    }
}
