// Copyright (c) 2013-2016 K Team. All Rights Reserved.

package org.kframework.kil;

import java.util.concurrent.ConcurrentHashMap;

/**
 * AST representation of a KLabel constant.
 */
public class KLabelConstant extends KLabel {

    /**
     * HashMap caches the constants to ensure uniqueness.
     */
    private static final ConcurrentHashMap<String, KLabelConstant> cache = new ConcurrentHashMap<>();

    /**
     * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant objects; subsequent calls with the same label return
     * the same object. As opposed to "of", does not inspect for list of productions. Should be used for builtins only.
     *
     * @param label
     *            string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the KLabel;
     */
    public static KLabelConstant of(String label) {
        assert label != null;
        return cache.computeIfAbsent(label, x -> new KLabelConstant(x));
    }

    /**
     * Checks whether this label corresponds to a predicate
     * @return true if the label denotes a predicate or false otherwise
     */
    public boolean isPredicate() {
        return  label.startsWith("is");
    }

    public String getLabel() {
        return label;
    }

    /* un-escaped label */
    private final String label;

    public KLabelConstant(String label) {
        this.label = label;
    }

    @Override
    public ASTNode shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KLabelConstant)) {
            return false;
        }

        KLabelConstant kLabelConstant = (KLabelConstant) object;
        return label.equals(kLabelConstant.label);
    }

    @Override
    public int hashCode() {
        return label.hashCode();
    }

    @Override
    public String toString() {
        return getLabel();
    }
}
