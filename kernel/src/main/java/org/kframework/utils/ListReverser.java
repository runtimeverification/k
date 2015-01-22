// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

public class ListReverser<T> implements Iterable<T> {
    private ListIterator<T> listIterator;
    public ListReverser(List<T> list) {
        this.listIterator = list.listIterator(list.size());
    }
    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {
            @Override
            public boolean hasNext() {
                return listIterator.hasPrevious();
            }
            @Override
            public T next() {
                return listIterator.previous();
            }
            @Override
            public void remove() {
                listIterator.remove();
            }
        };
    }
}
