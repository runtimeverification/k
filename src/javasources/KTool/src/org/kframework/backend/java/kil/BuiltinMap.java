package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import com.google.common.base.Joiner;


/**
 * @author AndreiS
 */
public class BuiltinMap extends Collection implements Sorted {

    public static final BuiltinMap EMPTY = new BuiltinMap();

    private final Map<Term, Term> entries;

    public BuiltinMap(Map<Term, Term> entries, Variable frame) {
        super(frame, Kind.KITEM);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public BuiltinMap(Variable frame) {
        super(frame, Kind.KITEM);
        entries = new HashMap<Term, Term>();
    }

    public BuiltinMap(Map<Term, Term> entries) {
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

    /**
     * Returns a {@code String} representation of the sort of this builtin map.
     */
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
        return super.equals(map) && entries.equals(map.entries);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + (super.frame == null ? 0 : super.frame.hashCode());
        hash = hash * Utils.HASH_PRIME + entries.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return toString(" ", " |-> ", ".Map");
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
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    public static BuiltinMap of(Map<Term, Term> entries, Term frame) {
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
