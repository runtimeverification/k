// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework;

import java.io.Serializable;
import java.util.Iterator;

public class List<T> implements Iterable<T>, Serializable {
    private final scala.collection.immutable.List<T> list;

    public List(scala.collection.immutable.List<T> l) {
        this.list = l;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {

            private scala.collection.immutable.List<T> l = list;

            @Override
            public boolean hasNext() {
                return !l.isEmpty();
            }

            @Override
            public T next() {
                T head = l.head();
                l = (scala.collection.immutable.List<T>) l.tail();
                return head;
            }
        };
    }
}
