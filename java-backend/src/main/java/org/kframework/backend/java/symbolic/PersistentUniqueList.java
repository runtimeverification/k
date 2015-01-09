package org.kframework.backend.java.symbolic;

import org.pcollections.HashTreePSet;
import org.pcollections.PSet;
import org.pcollections.PVector;
import org.pcollections.TreePVector;

import java.util.AbstractList;
import java.util.Collection;


/**
 */
public class PersistentUniqueList<E> extends AbstractList<E> implements PVector<E> {
    private static final PersistentUniqueList EMPTY = new PersistentUniqueList<>(
            TreePVector.empty(),
            HashTreePSet.empty());

    @SuppressWarnings("unchecked")
    public static <E> PersistentUniqueList<E> empty() {
        return EMPTY;
    }

    public static <E> PersistentUniqueList<E> singleton(E e) {
        return PersistentUniqueList.<E>empty().plus(e);
    }

    public static <E> PersistentUniqueList<E> from(Collection<E> collection) {
        return collection instanceof PersistentUniqueList ?
                (PersistentUniqueList<E>) collection :
                PersistentUniqueList.<E>empty().plusAll(collection);
    }

    private final PVector<E> contents;
    private final PSet<E> mark;

    private PersistentUniqueList(PVector<E> contents, PSet<E> mark) {
        this.contents = contents;
        this.mark = mark;
    }

    @Override
    public E get(int index) {
        return contents.get(index);
    }

    @Override
    public int size() {
        return contents.size();
    }

    @Override
    public PersistentUniqueList<E> plus(E e) {
        return !mark.contains(e) ?
                new PersistentUniqueList<>(contents.plus(e), mark.plus(e)) :
                this;
    }

    @Override
    public PersistentUniqueList<E> minus(Object o) {
        return mark.contains(o) ?
                new PersistentUniqueList<>(contents.minus(o), mark.minus(o)) :
                this;
    }

    @Override
    public PersistentUniqueList<E> plusAll(Collection<? extends E> collection) {
        PersistentUniqueList<E> result = this;
        for (E e : collection) {
            result = result.plus(e);
        }
        return result;
    }

    @Override
    public PersistentUniqueList<E> minusAll(Collection<?> collection) {
        PersistentUniqueList<E> result = this;
        for (Object o : collection) {
            result = result.minus(o);
        }
        return result;
    }

    @Override
    public PersistentUniqueList<E> plus(int i, E e) {
        return !mark.contains(e) ?
                new PersistentUniqueList<>(contents.plus(i, e), mark.plus(e)) :
                this;
    }

    @Override
    public PersistentUniqueList<E> minus(int i) {
        E e = contents.get(i);
        return new PersistentUniqueList<>(contents.minus(i), mark.minus(e));
    }

    @Override
    public PersistentUniqueList<E> with(int i, E e) {
        return minus(i).plus(i, e);
    }

    @Override
    public PersistentUniqueList<E> plusAll(int i, Collection<? extends E> collection) {
        PersistentUniqueList<E> result = this;
        for (E e : collection) {
            result = result.plus(i++, e);
        }
        return result;
    }

    @Override
    public PersistentUniqueList<E> subList(int start, int end) {
        return new PersistentUniqueList<>(
                contents.subList(start, end),
                HashTreePSet.from(contents.subList(start, end)));
    }
}
