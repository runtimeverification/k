package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import com.google.common.base.Joiner;


/**
 * Class representing a map. It only has one frame (which is a variable), and a set of entries.
 * A map composed of multiple map variables or terms (in addition to the entries) is represented
 * using concatenation (and can only occur in the right-hand side or in the condition).
 *
 * @author AndreiS
 */
public class BuiltinMap extends Collection {

    private final Map<Term, Term> entries;

    public BuiltinMap(Map<? extends Term, ? extends Term> entries, Variable frame) {
        super(frame, Kind.KITEM);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public BuiltinMap(Variable frame) {
        super(frame, Kind.KITEM);
        entries = new HashMap<Term, Term>();
    }

    public BuiltinMap(Map<? extends Term,? extends Term> entries) {
        super(null, Kind.KITEM);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public BuiltinMap() {
        super(null, Kind.KITEM);
        entries = new HashMap<Term, Term>();
    }

    public Term get(Term key) {
        return entries.get(key);
    }

    public Map<Term, Term> getEntries() {
        return Collections.unmodifiableMap(entries);
    }

    public Term put(Term key, Term value) {
        return entries.put(key, value);
    }

    public void putAll(Map<Term, Term> entries) {
        this.entries.putAll(entries);
    }

    public Term remove(Term key) {
        return entries.remove(key);
    }

    @Override
    public int size() {
        return entries.size();
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
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
            hashCode = hashCode * Utils.HASH_PRIME + entries.hashCode();
        }
        return hashCode;
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

    public static BuiltinMap of(Map<? extends Term, ? extends Term> entries, Term frame) {
        if (frame == null) {
            return new BuiltinMap(entries);
        }
        if (frame instanceof Variable)
            return new BuiltinMap(entries, (Variable) frame);
        if (frame instanceof BuiltinMap) {
            BuiltinMap builtinMap = (BuiltinMap) frame;
            builtinMap = new BuiltinMap(builtinMap.entries, builtinMap.frame);
            builtinMap.entries.putAll(entries);
            return builtinMap;
        }
        assert false : "Frame can only be substituted by a Variable or a BuiltinMap, or deleted.";
        return null;
    }
}
