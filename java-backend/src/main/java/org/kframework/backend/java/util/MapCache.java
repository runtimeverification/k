// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Supplier;

public class MapCache<K, V> {

    private final Map<K, V> cache;

    public MapCache(Map<K, V> cache) {
        this.cache = cache;
    }

    public MapCache() {
        this.cache = new HashMap<>();
    }

    public synchronized V get(K key, Supplier<V> value) {
        V cachedVal = cache.get(key);
        if (cachedVal == null) {
            cachedVal = value.get();
            cache.put(key, cachedVal);
        }
        return cachedVal;
    }
}
