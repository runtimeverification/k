// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.Lists;
import org.apache.commons.collections4.map.UnmodifiableMap;
import org.apache.commons.lang3.tuple.Triple;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.builtin.KLabels;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;


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
            GlobalContext global) {
        super(collectionPatterns, collectionFunctions, collectionVariables, global);
        this.entries = entries;
    }

    public static Term concatenate(GlobalContext global, Term... maps) {
        Builder builder = new Builder(global);
        builder.concatenate(maps);
        return builder.build();
    }

    public static Term concatenate(GlobalContext global, Collection<Term> maps) {
        Builder builder = new Builder(global);
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
        hashCode = hashCode * Constants.HASH_PRIME + entries.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionPatterns.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionFunctions.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionVariables.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return toString(" ", " |-> ", KLabels.DotMap.name());
    }

    private String toString(String operator, String mapsTo, String identity) {
        if (!isEmpty()) {
            IntToken key1 = IntToken.of(0);
            IntToken key2 = IntToken.of(2);
            if(entries.containsKey(key1) && entries.get(key1).toString().equals("PUSH(Int(#\"1\"),, Int(#\"0\"))") &&
               entries.containsKey(key2) && entries.get(key2).toString().equals("CALLDATALOAD_EVM(.KList)")) {
                return "CodeMap(" + entries.size() + ")";
            }
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
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public List<Term> getKComponents() {
        DataStructureSort sort = global.getDefinition().dataStructureSortOf(sort());

        ArrayList<Term> components = Lists.newArrayList();
        entries.entrySet().stream().forEach(entry ->
                components.add(KItem.of(
                        KLabelConstant.of(sort.elementLabel(), global.getDefinition()),
                        KList.concatenate(entry.getKey(), entry.getValue()),
                        global, entry.getKey().att())));

        for (Term term : baseTerms()) {
            if (term instanceof BuiltinMap) {
                components.addAll(((BuiltinMap) term).getKComponents());
            } else {
                components.add(term);
            }
        }

        return components;
    }

    public static Builder builder(GlobalContext global) {
        return new Builder(global);
    }

    public static class Builder {

        private final Map<Term, Term> entries = new HashMap<>();
        private final ImmutableMultiset.Builder<KItem> patternsBuilder = new ImmutableMultiset.Builder<>();
        private final ImmutableMultiset.Builder<Term> functionsBuilder = new ImmutableMultiset.Builder<>();
        private final ImmutableMultiset.Builder<Variable> variablesBuilder = new ImmutableMultiset.Builder<>();
        private final GlobalContext global;

        public Builder(GlobalContext global) {
            this.global = global;
        }

        public void put(Term key, Term value) {
            entries.put(key, value);
        }

        /**
         * Copies all key-javaBackendValue pairs of the given map into the BuiltinMap being
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

                if (!update && entries.keySet().stream().anyMatch(key -> map.entries.containsKey(key) && !entries.get(key).equals(map.entries.get(key)))) {
                    List<Triple<Term, Term, Term>> clashingKeys = entries.keySet().stream().filter(map.entries::containsKey).map(k -> Triple.of(k, entries.get(k), map.entries.get(k))).collect(Collectors.toList());
                    throw KEMException.criticalError("failed to concatenate maps with common keys: "
                            + clashingKeys);
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
                    global);
            return builtinMap.baseTerms().size() == 1 && builtinMap.collectionVariables().size() == 1 && builtinMap.concreteSize() == 0 ?
                    builtinMap.baseTerms().iterator().next() : builtinMap;
        }
    }
}
