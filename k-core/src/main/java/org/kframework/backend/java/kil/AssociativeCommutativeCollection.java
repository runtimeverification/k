// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.Multiset;
import com.google.common.collect.Multisets;


/**
 * Common parent for {@link org.kframework.backend.java.kil.BuiltinMap} and
 * {@link org.kframework.backend.java.kil.BuiltinSet}.
 */
public abstract class AssociativeCommutativeCollection extends Collection {

    protected final ImmutableMultiset<KItem> collectionPatterns;
    protected final ImmutableMultiset<Term> collectionFunctions;
    protected final ImmutableMultiset<Variable> collectionVariables;

    protected AssociativeCommutativeCollection(
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables) {
        super(computeFrame(collectionPatterns, collectionFunctions, collectionVariables), Kind.KITEM);
        this.collectionPatterns = collectionPatterns;
        this.collectionVariables = collectionVariables;
        this.collectionFunctions = collectionFunctions;
    }

    private static Variable computeFrame(
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables) {
        if (collectionPatterns.isEmpty() && collectionFunctions.isEmpty() && collectionVariables.size() == 1) {
            return collectionVariables.iterator().next();
        } else {
            return null;
        }
    }

    /**
     * Returns an unmodifiable view of the union of the patterns, functions and variables multisets.
     *
     * @see org.kframework.kil.CollectionBuiltin#baseTerms
     */
    public Multiset<Term> baseTerms() {
        return Multisets.union(
                Multisets.union(collectionPatterns, collectionFunctions),
                collectionVariables);
    }

    public ImmutableMultiset<KItem> collectionPatterns() {
        return collectionPatterns;
    }

    public ImmutableMultiset<Term> collectionFunctions() {
        return collectionFunctions;
    }

    public ImmutableMultiset<Variable> collectionVariables() {
        return collectionVariables;
    }

    @Override
    public final boolean isConcreteCollection() {
        return collectionPatterns.isEmpty()
                && collectionVariables.isEmpty()
                && collectionFunctions.isEmpty();
    }

    @Override
    public final boolean isEmpty() {
        return concreteSize() == 0 && isConcreteCollection();
    }

    @Override
    public final boolean isExactSort() {
        return true;
    }

    @Override
    public final boolean isGround() {
        return isConcreteCollection() && super.isGround();
    }

}
