// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

public class Annotated<T1, T2> {
    private final T1 obj;
    private final T2 ann;

    public Annotated(T1 obj, T2 ann) {
        assert(obj != null);
        this.obj = obj;
        this.ann = ann;
    }

    public T1 getObj() {
        return obj;
    }

    public T2 getAnn() {
        return ann;
    }

    @Override
    public int hashCode() {
        return obj.hashCode();
    }

    @Override
    public String toString() {
        return obj.toString() + " [" + ann.toString() + "]";
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Annotated)
            return ((Annotated) obj).getObj().equals(this.obj);
        return false;
    }
}
