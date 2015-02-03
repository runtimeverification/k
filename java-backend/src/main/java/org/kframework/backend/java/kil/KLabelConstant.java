// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Set;

import org.apache.commons.collections4.trie.PatriciaTrie;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.MapCache;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Production;

import com.google.common.collect.Multimap;


/**
 * A KLabel constant.
 *
 * @author AndreiS
 */
public class KLabelConstant extends KLabel implements MaximalSharing, org.kframework.kore.KLabel {

    /* KLabelConstant cache */
    private static final MapCache<Set<SortSignature>, MapCache<String, KLabelConstant>> cache = new MapCache<>();

    /* un-escaped label */
    private final String label;

    /* the sort signatures of the productions generating this {@code KLabelConstant} */
    private final Set<SortSignature> signatures;

    /* the attributes associated with the productions generating this {@code KLabelConstant}
     * (attributes are assumed to be identical for all productions) */
    private final Attributes attributes;

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

    private final String smtlib;

    private final Sort predicateSort;

    /**
     * Specifies if this {@code KLabelConstant} is a list label,
     * e.g. {@code '.List{"'_,_"}}.
     */
    private final boolean isListLabel;

    private KLabelConstant(String label, Set<SortSignature> signatures, Attributes attributes, Definition definition) {
        this.label = label;
        this.signatures = signatures;
        this.attributes = attributes;

        // TODO(YilongL): urgent; how to detect KLabel clash?

        boolean isFunction = false;
        boolean isPattern = false;
        String smtlib = null;
        if (!label.startsWith("is")) {
            predicateSort = null;
            isFunction = attributes.containsAttribute(Attribute.FUNCTION.getKey())
                    || attributes.containsAttribute(Attribute.PREDICATE.getKey());
            isPattern = attributes.containsAttribute(Attribute.PATTERN_KEY);
            smtlib = attributes.getAttribute(Attribute.SMTLIB_KEY);
        } else {
            /* a KLabel beginning with "is" represents a sort membership predicate */
            isFunction = true;
            predicateSort = Sort.of(label.substring("is".length()));
        }
        this.isSortPredicate = predicateSort != null;
        this.isFunction = isFunction;
        this.isPattern = isPattern;
        this.smtlib = smtlib;

        this.isListLabel = !definition.listLabelsOf(label).isEmpty();
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
        MapCache<String, KLabelConstant> trie = cache.get(definition.signaturesOf(label), () -> new MapCache<>(new PatriciaTrie<>()));
        return trie.get(label, () -> new KLabelConstant(label, definition.signaturesOf(label), definition.kLabelAttributesOf(label), definition));
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

    public String smtlib() {
        return smtlib;
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

    public boolean isListLabel() {
        return isListLabel;
    }

    /**
     * Returns the associated list terminator if this {@code KLabelConstant} is
     * a list label; otherwise, {@code null}.
     */
    public KItem getListTerminator(Definition definition) {
        if (!definition.listLabelsOf(label).isEmpty()) {
            Production production = definition.listLabelsOf(label).iterator().next();
            String separator = production.getListDecl().getSeparator();
            return new KItem(this, KList.EMPTY, Sort.SHARP_BOT.getUserListSort(separator), true);
        }
        return null;
    }

    public String label() {
        return label;
    }

    /**
     * Returns a list of productions generating this {@code KLabelConstant}.
     */
    public Set<SortSignature> signatures() {
        return signatures;
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
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
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
        MapCache<String, KLabelConstant> trie = cache.get(signatures, () -> new MapCache<>(new PatriciaTrie<>()));
        return trie.get(label, () -> this);
    }

    public String getAttribute(String attribute) {
        return attributes.getAttribute(attribute);
    }

    public boolean isMetaBinder() {
        return attributes.containsKey("metabinder");
    }

    public boolean isBinder() {
        return attributes.containsKey("binder");
    }

    /**
     * Searches for and retieves (if found) a binder map for this label
     * See {@link org.kframework.kil.Production#getBinderMap()}
     *
     * @return the binder map for this label (or {@code null} if no binder map was defined.
     */
    public Multimap<Integer, Integer> getBinderMap() {
        throw new UnsupportedOperationException();
    }
}
