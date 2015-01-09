package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.Sets;
import org.pcollections.HashPMap;
import org.pcollections.HashTreePMap;


/**
 */
// TODO(AndreiS): extend/implement KItem
public class Substitution<K extends Term, V extends Term> implements Map<K, V> {

    private static final Substitution EMPTY = new Substitution<>(
            HashTreePMap.<Term, Term>empty());

    @SuppressWarnings("unchecked")
    public static <K extends Term, V extends Term> Substitution<K, V> empty() {
        return EMPTY;
    }

    public static <K extends Term, V extends Term> Substitution<K, V> singleton(K key, V value) {
        return new Substitution<>(HashTreePMap.singleton(key, value));
    }

    public static <K extends Term, V extends Term> Substitution<K, V> from(Map<K, V> map) {
        return map instanceof Substitution ?
                (Substitution<K, V>) map :
                new Substitution<>(HashTreePMap.from(map));
    }

    @SuppressWarnings("unchecked")
    public static <K extends Term, V extends Term> Substitution<K, V> composeAndEvaluate(
            Substitution<? extends K, ? extends V> substitution1,
            Substitution<? extends K, ? extends V> substitution2,
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

        return new Substitution<>(entries);
    }

    private final HashPMap<K, V> entries;

    private Substitution(HashPMap<K, V> entries) {
        this.entries = entries;
    }

    public Substitution<K, V> plus(K key, V value) {
        if (entries.get(key) != null) {
            if (entries.get(key).equals(value)) {
                return this;
            } else {
                return null;
            }
        }
        return new Substitution<>(entries.plus(key, value));
    }

    @SuppressWarnings("unchecked")
    public Substitution<K, V> plusAll(Map<? extends K, ? extends V> substitution) {
        Substitution<K, V> result = this;
        for (Entry<K, V> entry : ((Map<K, V>) substitution).entrySet()) {
            result = result.plus(entry.getKey(), entry.getValue());
            if (result == null) {
                return null;
            }
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    public Substitution<K, V> evaluate(TermContext context) {
        HashPMap<K, V> entries = HashTreePMap.empty();
        for (Entry<K, V> entry : entries.entrySet()) {
            entries = entries.plus(entry.getKey(), (V) entry.getValue().evaluate(context));
        }
        return new Substitution<>(entries);
    }

    public boolean isFalse(TermContext context) {
        return entries.entrySet().stream()
                .allMatch(entry -> new Equality(entry.getKey(), entry.getValue(), context).truthValue() != TruthValue.FALSE);
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

        if (!(object instanceof Substitution)) {
            return false;
        }

        Substitution substitution = (Substitution) object;
        return entries.equals(substitution.entries);
    }

    @Override
    public int hashCode() {
        return entries.hashCode();
    }

}
