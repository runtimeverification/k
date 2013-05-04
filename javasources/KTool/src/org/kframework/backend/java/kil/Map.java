package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Collections;
import java.util.HashMap;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:59 PM
 * To change this template use File | Settings | File Templates.
 */
public class Map extends Collection {

    public static final Map EMPTY = new Map();

    private final java.util.Map<Term, Term> entries;

    public Map(java.util.Map<Term, Term> entries, Variable frame) {
        super(frame, Kind.MAP);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public Map(Variable frame) {
        super(frame, Kind.MAP);
        entries = new HashMap<Term, Term>();
    }

    public Map(java.util.Map<Term, Term> entries) {
        super(null, Kind.MAP);
        this.entries = new HashMap<Term, Term>(entries);
    }

    public Map() {
        super(null, Kind.MAP);
        entries = new HashMap<Term, Term>();
    }

    public Term get(Term key) {
        return entries.get(key);
    }

    public java.util.Map<Term, Term> getEntries() {
        //return Collections.unmodifiableMap(entries);
        return Collections.unmodifiableMap(entries);
    }

    public Term put(Term key, Term value) {
        return entries.put(key, value);
    }

    @Override
    public String toString() {
        return toString(" ", " |-> ", "." + Kind.MAP);
    }

    public String toString(String operator, String mapsTo, String identity) {
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

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
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
