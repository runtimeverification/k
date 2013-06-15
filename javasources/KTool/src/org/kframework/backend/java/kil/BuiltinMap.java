package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.HashMap;


/**
 * @author AndreiS
 */
public class BuiltinMap extends Collection {

    public static final BuiltinMap EMPTY = new BuiltinMap();

    private final java.util.Map<Term, Term> entries;

    public BuiltinMap(java.util.Map<Term, Term> entries, Variable frame) {
        super(frame, Kind.KITEM);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public BuiltinMap(Variable frame) {
        super(frame, Kind.KITEM);
        entries = new HashMap<Term, Term>();
    }

    public BuiltinMap(java.util.Map<Term, Term> entries) {
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

    public java.util.Map<Term, Term> getEntries() {
        return Collections.unmodifiableMap(entries);
    }

    public Term put(Term key, Term value) {
        return entries.put(key, value);
    }

    public void putAll(java.util.Map<Term, Term> entries) {
        this.entries.putAll(entries);
    }

    public Term remove(Term key) {
        return entries.remove(key);
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
            stringBuilder.append(super.getFrame());
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

}
