package org.kframework.kore;

import scala.collection.immutable.List;

import java.io.Serializable;
import java.util.Iterator;

/**
 * Created by dwightguth on 11/19/15.
 */
public class ListIterable<T> implements Iterable<T>, Serializable {
    private List<T> list;

    public ListIterable(List<T> l) {
        this.list = l;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {

            @Override
            public boolean hasNext() {
                return !list.isEmpty();
            }

            @Override
            public T next() {
                T head = list.head();
                list = (scala.collection.immutable.List<T>) list.tail();
                return head;
            }
        };
    }
}
