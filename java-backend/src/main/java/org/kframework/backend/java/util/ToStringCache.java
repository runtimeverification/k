// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.KItem;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Denis Bogdanas
 * Created on 31-Jan-19.
 */
public class ToStringCache {
    private Map<KItem, String> toStringCache = new HashMap<>();

    public String get(KItem kItem) {
        return toStringCache.get(kItem);
    }

    public void put(KItem kItem, String str) {
        toStringCache.put(kItem, str);
    }

    public void clear() {
        toStringCache.clear();
    }

    public int size() {
        return toStringCache.size();
    }
}
