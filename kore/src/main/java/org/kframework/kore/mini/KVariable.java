// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.Sort;
import scala.collection.Seq;

import static org.kframework.Collections.Seq;

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
    public Seq<Sort> params() {
        return Seq();
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

        KVariable kVariable = (KVariable) o;

        return name.equals(kVariable.name);

    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
}
