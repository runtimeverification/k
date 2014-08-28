// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;

import java.util.HashMap;
import java.util.Map;

import org.apache.commons.collections4.map.UnmodifiableMap;
import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMultiset;


/**
 * Class representing a map.
 *
 * @author AndreiS
 */
public class BuiltinMap extends AssociativeCommutativeCollection {

    public static final BuiltinMap EMPTY_MAP = (BuiltinMap) builder().build();
    private final UnmodifiableMap<Term, Term> entries;

    /**
     * Private efficient constructor used by {@link BuiltinMap.Builder}.
     */
    private BuiltinMap(
            UnmodifiableMap<Term, Term> entries,
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables) {
        super(collectionPatterns, collectionFunctions, collectionVariables);
        this.entries = entries;
    }

    public static Term concatenate(Term... maps) {
        Builder builder = new Builder();
        builder.concatenate(maps);
        return builder.build();
    }

    public static boolean isMapUnifiableByCurrentAlgorithm(Term term, Term otherTerm) {
        return term instanceof BuiltinMap && ((BuiltinMap) term).isUnifiableByCurrentAlgorithm()
                && otherTerm instanceof BuiltinMap && ((BuiltinMap) otherTerm).isUnifiableByCurrentAlgorithm();
    }

    public Term get(Term key) {
        return entries.get(key);
    }

    public UnmodifiableMap<Term, Term> getEntries() {
        return entries;
    }

    public boolean isUnifiableByCurrentAlgorithm() {
        return collectionFunctions.isEmpty() && collectionVariables.size() <= 1;
    }

    @Override
    public int concreteSize() {
        return entries.size();
    }

    @Override
    public Sort sort() {
        // TODO(AndreiS): track the original sort from the grammar
        return Sort.MAP;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinMap)) {
            return false;
        }

        BuiltinMap map = (BuiltinMap) object;
        return entries.equals(map.entries)
                && collectionPatterns.equals(map.collectionPatterns)
                && collectionFunctions.equals(map.collectionFunctions)
                && collectionVariables.equals(map.collectionVariables);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + entries.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionPatterns.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionFunctions.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionVariables.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        boolean hasCell = false;
        for (Map.Entry<Term, Term> entry : entries.entrySet()) {
            hasCell = hasCell || entry.getKey().isMutable() || entry.getValue().isMutable();
            if (hasCell) {
                return true;
            }
        }
        for (Term term : baseTerms()) {
            hasCell = hasCell || term.isMutable();
            if (hasCell) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        return toString(" ", " |-> ", DataStructureSort.DEFAULT_MAP_UNIT_LABEL);
    }

    private String toString(String operator, String mapsTo, String identity) {
        if (!isEmpty()) {
            return Joiner.on(operator).join(
                    Joiner.on(operator).withKeyValueSeparator(mapsTo).join(entries),
                    Joiner.on(operator).join(collectionPatterns),
                    Joiner.on(operator).join(collectionFunctions),
                    Joiner.on(operator).join(collectionVariables));
        } else {
            return identity;
        }
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

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {

        private Map<Term, Term> entries = new HashMap<>();
        private ImmutableMultiset.Builder<KItem> patternsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Term> functionsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Variable> variablesBuilder = new ImmutableMultiset.Builder<>();

        public void put(Term key, Term value) {
            entries.put(key, value);
        }

        /**
         * Copies all key-value pairs of the given map into the BuiltinMap being
         * built.
         */
        public void putAll(Map<? extends Term, ? extends Term> map) {
            entries.putAll(map);
        }

        public Term remove(Term key) {
            return entries.remove(key);
        }

        public Map<Term, Term> getEntries() {
            return UnmodifiableMap.unmodifiableMap(entries);
        }

        private void concatenate(Term term) {
            assert term.sort().equals(Sort.MAP)
            : "unexpected sort " + term.sort() + " of concatenated term " + term
            + "; expected " + Sort.MAP;

            if (term instanceof BuiltinMap) {
                BuiltinMap map = (BuiltinMap) term;
                entries.putAll(map.entries);
                patternsBuilder.addAll(map.collectionPatterns);
                functionsBuilder.addAll(map.collectionFunctions);
                variablesBuilder.addAll(map.collectionVariables);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isPattern()) {
                patternsBuilder.add((KItem) term);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isFunction()) {
                functionsBuilder.add(term);
            } else if (term instanceof MapUpdate) {
                functionsBuilder.add(term);
            } else if (term instanceof Variable) {
                variablesBuilder.add((Variable) term);
            } else {
                assert false : "unexpected concatenated term" + term;
            }
        }

        /**
         * Concatenates terms of sort Map to this builder.
         */
        public void concatenate(Term... terms) {
            for (Term term : terms) {
                concatenate(term);
            }
        }

        /**
         * Concatenates collection of terms of sort Map to this builder.
         */
        public void concatenate(java.util.Collection<Term> terms) {
            for (Term term : terms) {
                concatenate(term);
            }
        }

        public Term build() {
            // YilongL: Guava's ImmutableMap.copyOf(entries) is not smart enough
            // to avoid actually copying the entries, because entries is not an
            // ImmutableMap yet; using Apache's decorate method because it would
            // avoid creating nesting wrappers
            BuiltinMap builtinMap = new BuiltinMap(
                    (UnmodifiableMap<Term, Term>) UnmodifiableMap.unmodifiableMap(entries),
                    patternsBuilder.build(),
                    functionsBuilder.build(),
                    variablesBuilder.build());
            return builtinMap.hasFrame() && builtinMap.entries.isEmpty() ? builtinMap.frame : builtinMap;
        }
    }
}
