// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.Map;

import org.kframework.backend.java.kil.Immutable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.util.Profiler;

import com.rits.cloning.Cloner;

/**
 * Deep cloning utility class.
 *
 * @author YilongL
 *
 */
public class DeepCloner {

    private static final Cloner cloner = new FastTermCloner();

    static {
        cloner.dontCloneInstanceOf(Immutable.class);
    }

    public static Term clone(Term term) {
        Profiler.startTimer(Profiler.DEEP_CLONE_TIMER);
        Term deepClone = cloner.deepClone(term);
        Profiler.stopTimer(Profiler.DEEP_CLONE_TIMER);
        return deepClone;
    }

    /**
     * Besides {@link Immutable} terms, avoid cloning terms that are possibly
     * mutable but actually immutable at run-time. E.g., a {@code KItem} is
     * possibly but rarely mutable in practice.
     */
    private static class FastTermCloner extends Cloner {

        @Override
        protected Object fastClone(final Object o, final Map<Object, Object> clones) throws IllegalAccessException {
            if (o instanceof Term && !((Term) o).hasCell()) {
                return o;
            } else {
                return super.fastClone(o, clones);
            }
        }
    }

}
