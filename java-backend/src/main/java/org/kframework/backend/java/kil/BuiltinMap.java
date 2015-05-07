// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.apache.commons.collections4.map.UnmodifiableMap;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.Lists;


/**
 * Class representing a map.
 *
 * @author AndreiS
 */
public class BuiltinMap extends AssociativeCommutativeCollection {

    private final UnmodifiableMap<Term, Term> entries;

    /**
     * Private efficient constructor used by {@link BuiltinMap.Builder}.
     */
    private BuiltinMap(
            UnmodifiableMap<Term, Term> entries,
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables,
            TermContext context) {
        super(collectionPatterns, collectionFunctions, collectionVariables, context);
        this.entries = entries;
    }

    public static Term concatenate(TermContext context, Term... maps) {
        Builder builder = new Builder(context);
        builder.concatenate(maps);
        return builder.build();
    }

    public static Term concatenate(TermContext context, Collection<Term> maps) {
        Builder builder = new Builder(context);
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
        return collectionFunctions.isEmpty();
    }

    public boolean hasOnlyGroundKeys() {
        return entries.keySet().stream().allMatch(Term::isGround);
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

    @Override
    public List<Term> getKComponents() {
        DataStructureSort sort = context.definition().dataStructureSortOf(sort());

        ArrayList<Term> components = Lists.newArrayList();
        entries.entrySet().stream().forEach(entry ->
                components.add(KItem.of(
                        KLabelConstant.of(sort.elementLabel(), context.definition()),
                        KList.concatenate(entry.getKey(), entry.getValue()),
                        context, entry.getKey().getSource(), entry.getKey().getLocation())));

        for (Term term : baseTerms()) {
            if (term instanceof BuiltinMap) {
                components.addAll(((BuiltinMap) term).getKComponents());
            } else {
                components.add(term);
            }
        }

        return components;
    }

    public static Builder builder(TermContext context) {
        return new Builder(context);
    }

    public static class Builder {

        private Map<Term, Term> entries = new HashMap<>();
        private ImmutableMultiset.Builder<KItem> patternsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Term> functionsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Variable> variablesBuilder = new ImmutableMultiset.Builder<>();
        private final TermContext context;

        public Builder(TermContext context) {
            this.context = context;
        }

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

        private void concatenate(Term term, boolean update) {
            if (!term.sort().equals(Sort.MAP)) {
                throw KEMException.criticalError("unexpected sort "
                        + term.sort() + " of concatenated term " + term
                        + "; expected " + Sort.MAP);
            }

            if (term instanceof BuiltinMap) {
                BuiltinMap map = (BuiltinMap) term;

                if (!update && entries.keySet().stream().anyMatch(key -> map.entries.containsKey(key))) {
                    throw KEMException.criticalError("failed to concatenate maps with common keys: "
                            + entries.keySet().stream().filter(map.entries::containsKey).collect(Collectors.toList()));
                }

                entries.putAll(map.entries);
                patternsBuilder.addAll(map.collectionPatterns);
                functionsBuilder.addAll(map.collectionFunctions);
                variablesBuilder.addAll(map.collectionVariables);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isPattern()) {
                patternsBuilder.add((KItem) term);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isFunction()) {
                functionsBuilder.add(term);
            } else if (term instanceof Variable) {
                variablesBuilder.add((Variable) term);
            } else {
                throw KEMException.criticalError("unexpected concatenated term" + term);
            }
        }

        /**
         * Concatenates terms of sort Map to this builder.
         */
        public void concatenate(Term... terms) {
            for (Term term : terms) {
                concatenate(term, false);
            }
        }

        /**
         * Updates this builder with the specified terms of sort Map.
         */
        public void update(Term... terms) {
            for (Term term : terms) {
                concatenate(term, true);
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
                    variablesBuilder.build(),
                    context);
            return builtinMap.baseTerms().size() == 1 && builtinMap.concreteSize() == 0 ?
                    builtinMap.baseTerms().iterator().next() : builtinMap;
        }
    }
}
