// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Multimap;
import com.google.common.reflect.TypeToken;
import com.google.inject.name.Names;
import org.apache.commons.collections4.trie.PatriciaTrie;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicInteger;


/**
 * A KLabel constant.
 *
 * @author AndreiS
 */
public class KLabelConstant extends KLabel implements MaximalSharing, org.kframework.kore.KLabel {

    private static final ConcurrentMap<Pair<Set<SortSignature>, Attributes>,
            ConcurrentMap<String, KLabelConstant>> cache = new ConcurrentHashMap<>();

    /**
     * see {@link #ordinal()}
     */
    public static final AtomicInteger maxOrdinal = new AtomicInteger(0);

    /* un-escaped label */
    private final String label;

    /**
     * see {@link #ordinal()}
     */
    private final int ordinal;

    /* the sort signatures of the productions generating this {@code KLabelConstant} */
    private final Set<SortSignature> signatures;

    /* the attributes associated with the productions generating this {@code KLabelConstant}
     * (attributes are assumed to be identical for all productions) */
    private final Attributes productionAttributes;

    /*
     * boolean flag set iff a production tagged with "function" or "predicate"
     * generates this {@code KLabelConstant}
     */
    private final boolean isFunction;

    /*
     * boolean flag set iff a production tagged with "pattern" generates
     * this {@code KLabelConstant}
     */
    private final boolean isPattern;

    private final boolean isSortPredicate;

    private final Sort predicateSort;

    private final String smtlib;

    private KLabelConstant(
            String label,
            int ordinal,
            Set<SortSignature> signatures,
            Set<Sort> allSorts,
            Attributes productionAttributes) {
        this.label = label;
        this.ordinal = ordinal;
        this.signatures = signatures;
        this.productionAttributes = productionAttributes;

        // TODO(YilongL): urgent; how to detect KLabel clash?

        boolean isFunction;
        boolean isPattern = false;
        String smtlib = null;
        if (!label.startsWith("is") || !allSorts.contains(Sort.of(label.substring("is".length())))) {
            predicateSort = null;
            isFunction = productionAttributes.containsKey(Attribute.FUNCTION.getKey())
                    || productionAttributes.containsKey(Attribute.PREDICATE.getKey());
            isPattern = productionAttributes.containsKey(Attribute.keyOf(Attribute.PATTERN_KEY));
            Attribute<?> smtlibAttribute = productionAttributes.get(Attribute.keyOf(Attribute.SMTLIB_KEY));
            smtlib = smtlibAttribute != null ? (String) smtlibAttribute.getValue() : null;
        } else {
            /* a KLabel beginning with "is" represents a sort membership predicate */
            isFunction = true;
            predicateSort = Sort.of(label.substring("is".length()));
        }
        this.isSortPredicate = predicateSort != null;
        this.isFunction = isFunction;
        this.isPattern = isPattern;
        this.smtlib = smtlib;
    }

    /**
     * Returns a {@code KLabelConstant} representation of label. The {@code KLabelConstant}
     * instances are cached to ensure uniqueness (subsequent invocations
     * of this method with the same label return the same {@code KLabelConstant} object).
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the the KLabel;
     */
    public static KLabelConstant of(String label, Definition definition) {
        return cache.computeIfAbsent(Pair.of(definition.signaturesOf(label), definition.kLabelAttributesOf(label)), p -> new ConcurrentHashMap<>())
                .computeIfAbsent(label, l -> new KLabelConstant(
                        l,
                        maxOrdinal.getAndIncrement(),
                        definition.signaturesOf(l),
                        definition.allSorts(),
                        definition.kLabelAttributesOf(l)));
    }

    /**
     * Returns true iff no production tagged with "function" or "predicate" or "pattern"
     * generates this {@code KLabelConstant}.
     */
    @Override
    public boolean isConstructor() {
        return !isFunction;
    }

    /**
     * Returns true iff a production tagged with "function" or "predicate" generates this {@code
     * KLabelConstant}.
     */
    @Override
    public boolean isFunction() {
        return isFunction;
    }

    /**
     * Returns true iff a production tagged with "pattern" generates
     * this {@code KLabelConstant}.
     */
    @Override
    public boolean isPattern() {
        return isPattern;
    }

    /**
     * Returns true if this {@code KLabelConstant} is a sort membership
     * predicate; otherwise, false.
     */
    public boolean isSortPredicate() {
        return isSortPredicate;
    }

    /**
     * Returns the predicate sort if this {@code KLabelConstant} represents a
     * sort membership predicate; otherwise, {@code null}.
     */
    public Sort getPredicateSort() {
        assert isSortPredicate();
        return predicateSort;
    }

    public String label() {
        return label;
    }

    /**
     * @return an unique integer representing the KLabel -- used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
     */
    public int ordinal() {
        return ordinal;
    }

    /**
     * Returns a list of productions generating this {@code KLabelConstant}.
     */
    public Set<SortSignature> signatures() {
        return signatures;
    }

    /**
     * @return the SMTLIB name of this KLabel
     */
    public String smtlib() {
        return smtlib;
    }

    @Override
    public String name() {
        return label;
    }

    @Override
    public boolean equals(Object object) {
        /* {@code KLabelConstant} objects are cached to ensure uniqueness */
        return this == object;
    }

    @Override
    protected int computeHash() {
        return label.hashCode();
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public String toString() {
        return label;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if there is a cached
     * instance.
     */
    private Object readResolve() {
        Map<String, KLabelConstant> localCache = cache.computeIfAbsent(
                Pair.of(signatures, productionAttributes),
                p -> new ConcurrentHashMap<>());
        if (localCache.containsKey(label) && localCache.get(label).ordinal != this.ordinal) {
            KEMException.criticalError("The ordinal for klabel: " + label + " is " + localCache.get(label).ordinal +
                    " in the cache and " + this.ordinal + " serialized.");
        }
        // TODO: fix bug: ordinals from deserialized objects may overlap with those of newly created objects
        return localCache.computeIfAbsent(label, l -> this);
    }

    public String getAttr(String attribute) {
        return productionAttributes.getAttr(attribute);
    }

    public boolean isMetaBinder() {
        return getAttr("metabinder") != null;
    }

    public boolean isBinder() {
        return getAttr("binder") != null;
    }

    /**
     * Searches for and retrieves (if found) a binder map for this label
     * See {@link org.kframework.kil.Production#getBinderMap()}
     *
     * @return the binder map for this label (or {@code null} if no binder map was defined.
     */
    public Multimap<Integer, Integer> getBinderMap() {
        if (isBinder()) {
            Multimap<Integer, Integer> binder = productionAttributes.getAttr(Attribute.Key.get(
                    new TypeToken<Multimap<Integer, Integer>>() {},
                    Names.named("binder")));
            return binder == null ? ImmutableMultimap.of(0, 1) : binder;
        } else {
            return null;
        }
    }

    /**
     * Searches for and retrieves (if found) a meta binder map for this label
     * See {@link org.kframework.kil.Production#getBinderMap()}
     *
     * @return the binder map for this label (or {@code null} if no meta binder map was defined.
     */
    public Multimap<Integer, Integer> getMetaBinderMap() {
        if (isMetaBinder()) {
            return productionAttributes.getAttr(Attribute.Key.get(
                    new TypeToken<Multimap<Integer, Integer>>() {},
                    Names.named("metabinder")));
        } else {
            return null;
        }
    }

}
