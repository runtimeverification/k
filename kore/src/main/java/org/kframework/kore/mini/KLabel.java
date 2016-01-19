package org.kframework.kore.mini;

import org.kframework.attributes.Att;
import org.kframework.kore.*;

import java.util.Collections;
import java.util.List;
import java.util.stream.Stream;

/**
 * Created by dwightguth on 1/11/16.
 */
public class KLabel implements org.kframework.kore.KLabel, org.kframework.kore.KApply {

    private final String name;

    public KLabel(String name) {
        this.name = name;
    }

    @Override
    public String name() {
        return name;
    }

    @Override
    public org.kframework.kore.KLabel klabel() {
        return this;
    }

    private static final KList EMPTY_KLIST = new KList() {

        @Override
        public List<K> items() {
            return Collections.emptyList();
        }

        @Override
        public int size() {
            return 0;
        }

        @Override
        public Iterable<? extends K> asIterable() {
            return Collections.emptyList();
        }

        @Override
        public Stream<K> stream() {
            return Stream.empty();
        }

        @Override
        public int computeHashCode() {
            return hashCode();
        }
    };

    @Override
    public KList klist() {
        return EMPTY_KLIST;
    }

    @Override
    public List<K> items() {
        return Collections.emptyList();
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public Iterable<? extends K> asIterable() {
        return Collections.emptyList();
    }

    @Override
    public Stream<K> stream() {
        return Stream.empty();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        KLabel kLabel = (KLabel) o;

        return name.equals(kLabel.name);

    }

    @Override
    public int computeHashCode() {
        return hashCode();
    }

    @Override
    public Att att() {
        return Att.apply();
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public int cachedHashCode() {
        return hashCode();
    }
}
