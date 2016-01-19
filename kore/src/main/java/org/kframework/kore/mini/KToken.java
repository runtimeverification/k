package org.kframework.kore.mini;

import org.kframework.attributes.Att;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KToken implements org.kframework.kore.KToken {

    private final String s;
    private final String sort;

    public KToken(String s, String sort) {
        this.s = s;
        this.sort = sort;
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public Sort sort() {
        return new Sort(sort);
    }

    @Override
    public String s() {
        return s;
    }

    @Override
    public Att att() {
        return Att.apply();
    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KToken kToken = (KToken) o;

        if (!s.equals(kToken.s)) return false;
        return sort.equals(kToken.sort);

    }

    @Override
    public int hashCode() {
        int result = s.hashCode();
        result = 31 * result + sort.hashCode();
        return result;
    }
}
