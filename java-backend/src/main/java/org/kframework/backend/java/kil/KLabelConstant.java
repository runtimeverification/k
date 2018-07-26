// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableMultimap;
import com.google.common.collect.Multimap;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.Attribute;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.Seq;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;


/**
 * A KLabel constant.
 *
 * @author AndreiS
 */
public class KLabelConstant extends KLabel implements org.kframework.kore.KLabel {

    private static final ConcurrentMap<Pair<Set<SortSignature>, Att>,
            ConcurrentMap<String, KLabelConstant>> cache = new ConcurrentHashMap<>();

    /**
     * see {@link #ordinal()}
     */
    public static final AtomicInteger maxOrdinal = new AtomicInteger(0);

    /* un-escaped label */
    private final String label;
    private final Seq<org.kframework.kore.Sort> params;

    /**
     * see {@link #ordinal()}
     */
    private final int ordinal;

    /* the sort signatures of the productions generating this {@code KLabelConstant} */
    private final Set<SortSignature> signatures;

    /* the attributes associated with the productions generating this {@code KLabelConstant}
     * (attributes are assumed to be identical for all productions) */
    private final Att productionAttributes;

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

    private final boolean isImpure;

    private final List<Integer> projectionAtt;

    private KLabelConstant(
            String label,
            Seq<org.kframework.kore.Sort> params,
            int ordinal,
            Set<SortSignature> signatures,
            Set<Sort> allSorts,
            Att productionAttributes) {
        this.label = label;
        this.params = params;
        this.ordinal = ordinal;
        this.signatures = signatures;
        this.productionAttributes = productionAttributes;

        // TODO(YilongL): urgent; how to detect KLabel clash?

        boolean isFunction;
        boolean isPattern = false;
        String smtlib = null;
        List<Integer>  projectionAtt = null;
        // there are labels which are just predicates, but are not obligated to be sort membership predicates
        if (!productionAttributes.contains(Attribute.PREDICATE_KEY, org.kframework.kore.Sort.class)) {
            predicateSort = null;
            isFunction = productionAttributes.contains(Attribute.FUNCTION_KEY);
            isPattern = productionAttributes.contains(Attribute.PATTERN_KEY);
            smtlib = productionAttributes.getOptional(Attribute.SMTLIB_KEY).orElse(null);
            projectionAtt = getProjectionAtt(productionAttributes);
        } else {
            /* a KLabel beginning with "is" represents a sort membership predicate */
            isFunction = true;
            predicateSort = Sort.of(productionAttributes.get(Attribute.PREDICATE_KEY, org.kframework.kore.Sort.class));
        }
        this.isSortPredicate = predicateSort != null;
        this.isFunction = isFunction;
        this.projectionAtt = projectionAtt;
        this.isPattern = isPattern;
        this.smtlib = smtlib;
        this.isImpure = productionAttributes.contains(Attribute.IMPURE_KEY);
    }

    /**
     * Returns a {@code KLabelConstant} representation of label. The {@code KLabelConstant}
     * instances are cached to ensure uniqueness (subsequent invocations
     * of this method with the same label return the same {@code KLabelConstant} object).
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the the KLabel;
     */
    public static KLabelConstant of(org.kframework.kore.KLabel label, Definition definition) {
        return cache.computeIfAbsent(Pair.of(definition.signaturesOf(label.name()), definition.kLabelAttributesOf(label)), p -> new ConcurrentHashMap<>())
                .computeIfAbsent(label.toString(), l -> new KLabelConstant(
                        label.name(),
                        label.params(),
                        maxOrdinal.getAndIncrement(),
                        definition.signaturesOf(label.name()),
                        definition.allSorts(),
                        definition.kLabelAttributesOf(label)));
    }

    /*
     * [proj(A,B,C)]  =>  (A,B,C)
     * [proj]         =>  (0,1,2)  // by default
     */
    private List<Integer> getProjectionAtt(Att productionAttributes) {
        Optional<String> proj = productionAttributes.getOptional(Attribute.PROJECTION_KEY);
        if (proj.isPresent()) {
            String projAtt = proj.get();
            if (projAtt.isEmpty()) {
                return Arrays.asList(0,1,2);
            } else {
                return Arrays.stream(proj.get().split(",")).map(s -> Integer.valueOf(s.trim())).collect(Collectors.toList());
            }
        } else {
            return null;
        }
    }

    public List<Integer> getProjectionAtt() {
        return projectionAtt;
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

    @Override
    public boolean isProjection() {
        return projectionAtt != null;
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

    public boolean isImpure() {
        return isImpure;
    }

    @Override
    public String name() {
        return label;
    }

    @Override
    public Seq<org.kframework.kore.Sort> params() { return params; }

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
    public String toString() {
        return label;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
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
            throw KEMException.criticalError("The ordinal for klabel: " + label + " is " + localCache.get(label).ordinal +
                    " in the cache and " + this.ordinal + " serialized.");
        }
        // TODO: fix bug: ordinals from deserialized objects may overlap with those of newly created objects
        return localCache.computeIfAbsent(label, l -> this);
    }

    public String getAttr(String attribute) {
        return productionAttributes.getOptional(attribute).orElse(null);
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
            Multimap<Integer, Integer> binder = productionAttributes.getOptional("binder", Multimap.class).orElse(null);
            assert signatures.stream().map(s -> s.parameters().size()).distinct().count() == 1;
            return binder == null ? ImmutableMultimap.of(0, signatures.iterator().next().parameters().size() - 1) : binder;
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
            return productionAttributes.get("metabinder", Multimap.class);
        } else {
            return null;
        }
    }

}
