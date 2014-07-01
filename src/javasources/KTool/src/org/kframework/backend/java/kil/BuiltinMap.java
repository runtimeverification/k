// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.collections15.map.UnmodifiableMap;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;


/**
 * Class representing a map.
 *
 * @author AndreiS
 */
public class BuiltinMap extends Collection {

    public static final BuiltinMap EMPTY_MAP = new BuiltinMap(
            (UnmodifiableMap<Term, Term>) UnmodifiableMap.decorate(Collections.<Term, Term>emptyMap()),
            ImmutableList.<KItem>of(),
            ImmutableList.<Variable>of(),
            ImmutableList.<Term>of());
    
    private final UnmodifiableMap<Term, Term> entries;
    private final ImmutableList<KItem> mapPatterns;
    private final ImmutableList<Variable> mapVariables;
    private final ImmutableList<Term> mapFunctions;

    /**
     * Private efficient constructor used by {@link BuiltinMap.Builder}.
     */
    private BuiltinMap(
            UnmodifiableMap<Term, Term> entries,
            ImmutableList<KItem> mapPatterns,
            ImmutableList<Variable> mapVariables,
            ImmutableList<Term> mapFunctions) {
        super(null, Kind.KITEM);
        this.entries = entries;
        this.mapPatterns = mapPatterns;
        this.mapVariables = mapVariables;
        this.mapFunctions = mapFunctions;
    }

    public static Term concatenate(Term... maps) {
        Builder builder = new Builder();
        builder.concatenate(maps);
        return builder.build();
    }

    public Term get(Term key) {
        return entries.get(key);
    }

    public UnmodifiableMap<Term, Term> getEntries() {
        return entries;
    }

    public ImmutableList<KItem> mapPatterns() {
        return mapPatterns;
    }

    public ImmutableList<Variable> mapVariables() {
        return mapVariables;
    }

    public ImmutableList<Term> mapFunctions() {
        return mapFunctions;
    }

    public boolean isEntryBuiltinMap() {
        return mapPatterns.isEmpty() && mapVariables.isEmpty() && mapFunctions.isEmpty();
    }

    public boolean isUnifiableByCurrentAlgorithm() {
        return mapFunctions.isEmpty() && mapVariables.size() <= 1;
    }

    @Override
    public boolean isEmpty() {
        return entries.isEmpty()
                && mapPatterns.isEmpty()
                && mapVariables.isEmpty()
                && mapFunctions.isEmpty();
    }

    @Override
    public int size() {
        return entries.size();
    }

    /**
     * {@code BuiltinMap} is guaranteed to have only one frame; thus, they can
     * always be used in the left-hand side of a rule.
     */
    @Override
    public boolean isLHSView() {
        // TODO(YilongL): allow BuiltinMap to have a list of Terms instead of
        // just substitution entries; revise the javadoc
        return true;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public String sort() {
        // TODO(AndreiS): track the original sort from the grammar
        return KSorts.MAP;
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
                && mapPatterns.equals(map.mapPatterns)
                && mapVariables.equals(map.mapVariables)
                && mapFunctions.equals(map.mapFunctions);
    }

    @Override
    public int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + entries.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + mapPatterns.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + mapVariables.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + mapFunctions.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return toString(" ", " |-> ", ".Map");
    }

    private String toString(String operator, String mapsTo, String identity) {
        if (!isEmpty()) {
            return Joiner.on(operator).join(
                    Joiner.on(operator).withKeyValueSeparator(mapsTo).join(entries),
                    Joiner.on(operator).join(mapPatterns),
                    Joiner.on(operator).join(mapVariables),
                    Joiner.on(operator).join(mapFunctions));
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
        private ImmutableList.Builder<KItem> patternsBuilder = new ImmutableList.Builder<>();
        private ImmutableList.Builder<Variable> variablesBuilder = new ImmutableList.Builder<>();
        private ImmutableList.Builder<Term> functionsBuilder = new ImmutableList.Builder<>();

        public void put(Term key, Term value) {
            entries.put(key, value);
        }
        
        /**
         * Copies all key-value pairs of the given map into the BuiltinMap being
         * built.
         */
        public void putAll(Map<Term, Term> map) {
            entries.putAll(map);
        }
        
        public Term remove(Term key) {
            return entries.remove(key);
        }
        
        public Map<Term, Term> getEntries() {
            return UnmodifiableMap.decorate(entries);
        }

        /**
         * Concatenates the BuiltinMap being built with another term, which can only
         * be a {@code Variable} or {@code BuiltinMap}.
         */
        public void concatenate(Term... terms) {
            for (Term term : terms) {
                assert term.sort().equals(KSorts.MAP)
                        : "unexpected sort " + term.sort() + " of concatenated term " + term
                        + "; expected " + KSorts.MAP;

                if (term instanceof BuiltinMap) {
                    BuiltinMap map = (BuiltinMap) term;
                    entries.putAll(map.entries);
                    patternsBuilder.addAll(map.mapPatterns);
                    variablesBuilder.addAll(map.mapVariables);
                    functionsBuilder.addAll(map.mapFunctions);
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
        }
        
        public Term build() {
            // YilongL: Guava's ImmutableMap.copyOf(entries) is not smart enough
            // to avoid actually copying the entries, because entries is not an
            // ImmutableMap yet; using Apache's decorate method because it would
            // avoid creating nesting wrappers
            BuiltinMap builtinMap = new BuiltinMap(
                    (UnmodifiableMap<Term, Term>) UnmodifiableMap.decorate(entries),
                    patternsBuilder.build(),
                    variablesBuilder.build(),
                    functionsBuilder.build());
            if (builtinMap.mapVariables.size() == 1
                    && builtinMap.entries.isEmpty()
                    && builtinMap.mapPatterns.isEmpty()
                    && builtinMap.mapFunctions.isEmpty()) {
                return builtinMap.mapVariables.get(0);
            } else {
                return builtinMap;
            }
        }
    }
}
