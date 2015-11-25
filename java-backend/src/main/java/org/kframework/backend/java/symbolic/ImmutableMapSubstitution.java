// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;
import org.pcollections.HashPMap;
import org.pcollections.HashTreePMap;

// TODO(AndreiS): extend/implement KItem
/**
 * Immutable-map-backed implementation of {@link Substitution}
 */
public class ImmutableMapSubstitution<K extends Term, V extends Term> implements Substitution<K,V>, Serializable {

    private static final ImmutableMapSubstitution EMPTY = new ImmutableMapSubstitution<>(
            HashTreePMap.<Term, Term>empty());

    @SuppressWarnings("unchecked")
    public static <K extends Term, V extends Term> ImmutableMapSubstitution<K, V> empty() {
        return EMPTY;
    }

    public static <K extends Term, V extends Term> ImmutableMapSubstitution<K, V> singleton(K key, V value) {
        return new ImmutableMapSubstitution<>(HashTreePMap.singleton(key, value));
    }

    public static <K extends Term, V extends Term> ImmutableMapSubstitution<K, V> from(Map<K, V> map) {
        return map instanceof ImmutableMapSubstitution ?
                (ImmutableMapSubstitution<K, V>) map :
                new ImmutableMapSubstitution<>(HashTreePMap.from(map));
    }

    @SuppressWarnings("unchecked")
    public static <K extends Term, V extends Term> ImmutableMapSubstitution<K, V> composeAndEvaluate(
            Substitution<? extends K, ? extends V> substitution1,
            ImmutableMapSubstitution<? extends K, ? extends V> substitution2,
            TermContext context) {
        // on substitution composition: http://www.mathcs.duq.edu/simon/Fall04/notes-7-4/node4.html
        assert Sets.intersection(substitution1.keySet(), substitution2.keySet()).isEmpty() :
                "There shall be no common variables in the two substitution maps to be composed.";
        assert substitution2.keySet().stream().allMatch(key -> key instanceof Variable) :
                "Substitution composition is only supported for Variable -> Term substitutions";

        HashPMap<K, V> entries = (HashPMap<K, V>) substitution2.entries;
        for (Entry<K, V> entry : ((Map<K, V>) substitution1).entrySet()) {
            entries = entries.plus(
                    entry.getKey(),
                    (V) entry.getValue().substituteAndEvaluate((Map<Variable, Term>) substitution2, context));
        }

        return new ImmutableMapSubstitution<>(entries);
    }

    private final HashPMap<K, V> entries;

    private ImmutableMapSubstitution(HashPMap<K, V> entries) {
        this.entries = entries;
    }

    @Override
    public ImmutableMapSubstitution<K, V> plus(K key, V value) {
        if (entries.get(key) != null) {
            if (entries.get(key).equals(value)) {
                return this;
            } else {
                return null;
            }
        }
        return new ImmutableMapSubstitution<>(entries.plus(key, value));
    }

    @Override
    public ImmutableMapSubstitution<K, V> minus(K key) {
        return new ImmutableMapSubstitution<>(entries.minus(key));
    }

    @Override
    public ImmutableMapSubstitution<K, V> minusAll(Collection<? extends K> keys) {
        return new ImmutableMapSubstitution<>(entries.minusAll(keys));
    }

    @Override
    @SuppressWarnings("unchecked")
    public ImmutableMapSubstitution<K, V> evaluate(TermContext context) {
        HashPMap<K, V> evaluatedEntries = HashTreePMap.empty();
        for (Entry<K, V> entry : entries.entrySet()) {
            evaluatedEntries = evaluatedEntries.plus(
                    entry.getKey(),
                    (V) entry.getValue().evaluate(context));
        }
        return new ImmutableMapSubstitution<>(evaluatedEntries);
    }

    @Override
    public List<Equality> equalities(GlobalContext global) {
        return entries.entrySet().stream()
                .map(entry -> new Equality(entry.getKey(), entry.getValue(), global))
                .collect(Collectors.toList());
    }

    @Override
    public boolean isFalse(GlobalContext global) {
        return equalities(global).stream().anyMatch(e -> e.truthValue() == TruthValue.FALSE);
    }

    @Override
    public int size() {
        return entries.size();
    }

    @Override
    public boolean isEmpty() {
        return entries.isEmpty();
    }

    @Override
    public boolean containsKey(Object key) {
        return entries.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return entries.containsValue(value);
    }

    @Override
    public V get(Object key) {
        return entries.get(key);
    }

    @Override
    public V put(K key, V value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public V remove(Object key) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void putAll(Map<? extends K, ? extends V> map) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<K> keySet() {
        return entries.keySet();
    }

    @Override
    public Collection<V> values() {
        return entries.values();
    }

    @Override
    public Set<Entry<K, V>> entrySet() {
        return entries.entrySet();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ImmutableMapSubstitution)) {
            return false;
        }

        ImmutableMapSubstitution substitution = (ImmutableMapSubstitution) object;
        return entries.equals(substitution.entries);
    }

    @Override
    public int hashCode() {
        return entries.hashCode();
    }

    @Override
    public String toString() {
        return entries.toString();
    }

    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.writeObject(new HashMap<>(entries));
    }

    @SuppressWarnings("unchecked")
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        try {
            Field entriesField = getClass().getDeclaredField("entries");
            entriesField.setAccessible(true);
            entriesField.set(this, HashTreePMap.from((Map<K, V>) in.readObject()));
        } catch (IllegalAccessException | NoSuchFieldException e) {
            throw new IOException(e);
        }
    }

    private void readObjectNoData() throws ObjectStreamException {
        throw new InvalidObjectException("Stream data required");
    }
}
