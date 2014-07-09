// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.apache.commons.collections15.map.UnmodifiableMap;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;


/**
 * Class representing a map. It only has one frame (which is a variable), and a set of entries.
 * A map composed of multiple map variables or terms (in addition to the entries) is represented
 * using concatenation (and can only occur in the right-hand side or in the condition).
 *
 * @author AndreiS
 */
public class BuiltinMap extends Collection implements Iterable<Map.Entry<Term, Term>> {

    public static final BuiltinMap EMPTY_MAP = new BuiltinMap();
    
    private final Map<Term, Term> entries;
    
    private BuiltinMap() {
        super(null, Kind.KITEM);
        entries = Collections.emptyMap();
    }

    public Term get(Term key) {
        return entries.get(key);
    }

    public Map<Term, Term> getEntries() {
        return UnmodifiableMap.decorate(entries);
    }

    @Override
    public Iterator<Map.Entry<Term, Term>> iterator() {
        return entries.entrySet().iterator();
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
        return (frame == null ? map.frame == null : frame.equals(map.frame))
                && entries.equals(map.entries);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
        hashCode = hashCode * Utils.HASH_PRIME + entries.hashCode();
        return hashCode;
    }
    
    @Override
    protected boolean computeHasCell() {
        boolean hasCell = false;
        for (Map.Entry<Term, Term> entry : entries.entrySet()) {
            hasCell = hasCell || entry.getKey().hasCell() || entry.getValue().hasCell();
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
        Joiner.MapJoiner joiner = Joiner.on(operator).withKeyValueSeparator(mapsTo);
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, entries);
        if (super.hasFrame()) {
            if (stringBuilder.length() != 0) {
                stringBuilder.append(operator);
            }
            stringBuilder.append(super.frame());
        }
        if (stringBuilder.length() == 0) {
            stringBuilder.append(identity);
        }
        return stringBuilder.toString();
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
     * Private efficient constructor used by {@link BuiltinMap.Builder}.
     * @param entries
     * @param frame
     */
    private BuiltinMap(UnmodifiableMap<Term, Term> entries, Variable frame) {
        super(frame, Kind.KITEM);
        this.entries = entries;
    }

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {
        
        private boolean done = false;
        
        private Map<Term, Term> entries = new HashMap<>();
        private Variable frame = null;

        public void put(Term key, Term value) {
            entries.put(key, value);
        }
        
        /**
         * Copies all key-value pairs of the given map into the BuiltinMap being
         * built.
         * 
         * @param map
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
         * Sets the entries as the given {@code BuiltinMap} without copying the
         * contents. Once the entries are set, no more modification is allowed.
         * 
         * @param map
         */
        public void setEntriesAs(BuiltinMap builtinMap) {
            // builtinMap.entries must be an UnmodifiableMap
            entries = builtinMap.entries;
        }
        
        /**
         * Sets the frame of the BuiltinMap being built. Once the frame is set,
         * it cannot be changed.
         * 
         * @param frame
         */
        public void setFrame(Variable frame) {
            this.frame = frame;
        }
        
        /**
         * Concatenates the BuiltinMap being built with another term, which can only
         * be a {@code Variable} or {@code BuiltinMap}.
         * 
         * @param term
         */
        public void concat(Term term) {
            if (term == null) {
                return;
            }
            
            if (term instanceof Variable) {
                setFrame((Variable) term);
            } else if (term instanceof BuiltinMap) {
                BuiltinMap map = (BuiltinMap) term;
                putAll(map.entries);
                if (map.frame != null) {
                    setFrame(map.frame);
                }
            } else {
                assert false : "The concatenated term must be a Variable or BuiltinMap; found: " + term;
            }
        }
        
        public BuiltinMap build() {
            Preconditions.checkArgument(!done, "Only one BuiltinMap can be built from a builder.");
            done = true;
            // YilongL: Guava's ImmutableMap.copyOf(entries) is not smart enough
            // to avoid actually copying the entries, because entries is not an
            // ImmutableMap yet; using Apache's decorate method because it would
            // avoid creating nesting wrappers
            return new BuiltinMap((UnmodifiableMap<Term, Term>) UnmodifiableMap.decorate(entries), frame);
        }
    }
}
