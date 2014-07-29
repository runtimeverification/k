package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableMultiset;


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
        super(null, Kind.KITEM);
        this.collectionPatterns = collectionPatterns;
        this.collectionVariables = collectionVariables;
        this.collectionFunctions = collectionFunctions;
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

    /**
     * Returns true if this collection consists only of elements or entries, but no patterns, functions or variables.
     * TODO: improve name/description
     */
    public boolean isConcreteCollection() {
        return collectionPatterns.isEmpty() && collectionVariables.isEmpty() && collectionFunctions.isEmpty();
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isGround() {
        return isConcreteCollection() && super.isGround();
    }

    @Override
    public boolean isLHSView() {
        // TODO(AndreiS): this method should be removed in later commits
        throw new UnsupportedOperationException();
    }

}
