// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.kore.KLabel;
import org.kframework.attributes.Att;

/**
 * Created by dwightguth on 1/11/16.
 */
public class InjectedKLabel implements org.kframework.kore.InjectedKLabel {

    private final KLabel klabel;

    public InjectedKLabel(KLabel klabel) {
        this.klabel = klabel;
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public KLabel klabel() {
        return klabel;
    }

    @Override
    public Att att() {
        return Att.empty();
    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        InjectedKLabel that = (InjectedKLabel) o;

        return klabel.equals(that.klabel);

    }

    @Override
    public int hashCode() {
        return klabel.hashCode();
    }
}
