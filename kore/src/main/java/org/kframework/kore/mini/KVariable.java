package org.kframework.kore.mini;

import org.kframework.attributes.Att;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KVariable implements org.kframework.kore.KVariable {

    private final String name;

    public KVariable(String name) {
        this.name = name;
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }

    @Override
    public String name() {
        return name;
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

        KVariable kVariable = (KVariable) o;

        return name.equals(kVariable.name);

    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
}
