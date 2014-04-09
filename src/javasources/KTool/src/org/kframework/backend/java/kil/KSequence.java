package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.kil.ASTNode;


/**
 * Represents a list of KItem, or {@link KItem} in the Java backend. Or in the
 * usual syntax of K, it can be defined as the following:
 * <p>
 * <blockquote>
 * 
 * <pre>
 * syntax K ::= List{KItem}{"~>"}
 * </pre>
 * 
 * </blockquote>
 * <p>
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class KSequence extends KCollection {

    private static final String SEPARATOR_NAME = " ~> ";
    private static final String IDENTITY_NAME = "." + Kind.K;
    
    private String sort;
    
    public KSequence(ImmutableList<Term> items, Variable frame) {
        super(items, frame, Kind.K);
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator, Variable frame) {
        super(itemsIterator, frame, "KSequence");
    }
    */

    public KSequence(Variable frame) {
        super(frame, Kind.K);
    }

    public KSequence(ImmutableList<Term> items) {
        super(items, null, Kind.K);
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator) {
        super(itemsIterator, null, "KSequence");
    }
    */

    public KSequence() {
        super(null, Kind.K);
    }

    @Override
    public KCollection fragment(int fromIndex) {
        return new KSequence(contents.subList(fromIndex, contents.size()), frame);
    }

    @Override
    public String sort() {
        if (sort != null) {
            return sort;
        }

        sort = size() == 1 && !hasFrame() ? contents.get(0).sort() : KSorts.KSEQUENCE;
        return sort;
    }

    @Override
    public String getSeparatorName() {
        return KSequence.SEPARATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KSequence.IDENTITY_NAME;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KSequence)) {
            return false;
        }

        KSequence kSequence = (KSequence) object;
        return (frame == null ? kSequence.frame == null : frame
                .equals(kSequence.frame))
                && contents.equals(kSequence.contents);
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
}
