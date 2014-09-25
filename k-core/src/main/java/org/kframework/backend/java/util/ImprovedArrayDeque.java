// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;


import java.util.*;

/**
 * @author Traian
 */
public class ImprovedArrayDeque<Element> extends ArrayDeque<Element> {

    public ImprovedArrayDeque(Collection<Element> elements) {
        super(elements);
    }

    public ImprovedArrayDeque() {
        super();
    }

    @Override
    public int hashCode() {
        int hashcode = 1;
        for (Element e : this) {
            hashcode = hashcode * Utils.HASH_PRIME + (e == null ? 0 : e.hashCode());
        }
        return hashcode;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof Deque)) return false;
        Iterator<Element> e1 = iterator();
        Iterator e2 = ((Deque) obj).iterator();
        while (e1.hasNext() && e2.hasNext()) {
            Element o1 = e1.next();
            Object o2 = e2.next();
            if (!(o1 == null ? o2 == null : o1.equals(o2)))
                return  false;
        }
        return !(e1.hasNext() || e2.hasNext());
    }
}
