// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.NoSuchElementException;

/**
 * A primitive doubly-linked list which was created in order to allow certain operations
 * to occur in constant time which java.util.LinkedList did not.
 * Currently only enough functionality is supported
 * to be able to handle the behavior of AbstractUnifier.
 * @param <E>
 */
public class DoubleLinkedList<E> {

    private static class Entry<E> {
        private E value;
        private Entry<E> next;
        private Entry<E> prev;

        Entry(E value, Entry<E> next, Entry<E> prev) {
            this.value = value;
            this.next = next;
            this.prev = prev;
        }
    }

    private Entry<E> head;
    private Entry<E> tail;

    public void clear() {
        head = tail = null;
    }

    public boolean isEmpty() {
        return head == null;
    }

    public void add(E e) {
        Entry<E> entry = new Entry<>(e, null, tail);
        if (tail == null) {
            head = tail = entry;
        } else {
            tail.next = entry;
            tail = entry;
        }
    }

    public E pop() {
        if (head == null) {
            throw new NoSuchElementException();
        } else {
            Entry<E> entry = head;
            head = entry.next;
            entry.next = null;
            if (head == null)
                tail = null;
            else
                head.prev = null;
            return entry.value;
        }
    }

    /**
     * Appends the specified list to the front of this list in constant time.
     * Because references to elements in {@code list} are no longer safe after becoming
     * part of another list reference, the specified {@code list} is cleared
     * and becomes empty.
     *
     * @param list
     */
    public void pushAll(DoubleLinkedList<E> list) {
        Entry<E> listLast = list.tail;
        if (listLast == null)
            return;
        Entry<E> thisFirst = this.head;
        if (thisFirst == null) {
            this.head = list.head;
            this.tail = list.tail;
            list.clear();
            return;
        }
        listLast.next = thisFirst;
        thisFirst.prev = listLast;
        this.head = list.head;
        list.clear();
    }
}
