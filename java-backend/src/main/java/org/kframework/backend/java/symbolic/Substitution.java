// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import java.util.Collection;
import java.util.List;
import java.util.Map;


public interface Substitution<K extends Term, V extends Term> extends Map<K, V> {
    Substitution<K, V> plus(K key, V value);

    @SuppressWarnings("unchecked")
    default Substitution<K, V> plusAll(Map<? extends K, ? extends V> substitution) {
        Substitution<K, V> result = this;
        for (Entry<K, V> entry : ((Map<K, V>) substitution).entrySet()) {
            result = result.plus(entry.getKey(), entry.getValue());
            if (result == null) {
                return null;
            }
        }
        return result;
    }

    Substitution<K, V> minus(K key);

    Substitution<K, V> minusAll(Collection<? extends K> keys);

    Substitution<K, V> evaluate(TermContext context);

    List<Equality> equalities(GlobalContext global);

    boolean isFalse(GlobalContext global);
}
