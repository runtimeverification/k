// Copyright (c) 2015-2016 K Team. All Rights Reserved.

package org.kframework.kore;

import scala.collection.Set;
import org.kframework.Collections;

/**
 * Folds a K term into a Set of Es.
 */
public class FoldKIntoSet<E> extends AbstractFoldK<Set<E>> {
    @Override
    public Set<E> unit() {
        return Collections.<E>Set();
    }

    @Override
    public Set<E> merge(Set<E> a, Set<E> b) {
        return Collections.or(a, b);
    }

    public Set<E> apply(K k) {
        return super.apply(k);
    }
}
