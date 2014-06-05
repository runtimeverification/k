// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.List;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableList;


/**
 * Represents a list of K, or {@link KSequence} in the Java backend. Or in the
 * usual syntax of K, it can be defined as the following:
 * <p>
 * <blockquote>
 * 
 * <pre>
 * syntax KList ::= List{K}{","}
 * </pre>
 * 
 * </blockquote>
 * <p>
 * 
 * @author AndreiS
 */
@SuppressWarnings("serial")
public class KList extends KCollection {

    private static final String SEPARATOR_NAME = ",, ";
    private static final String IDENTITY_NAME = "." + Kind.KLIST;
    public static final KList EMPTY = new KList((Variable) null);
    
    /**
     * A list of {@code Term}s contained in this {@code KList}.
     */
    private ImmutableList<Term> contents;
    
    private String sort;

    public KList(List<Term> items, Variable frame) {
        super(frame, Kind.KLIST);

        ImmutableList.Builder<Term> normalizedItemsBuilder = ImmutableList.builder();
        for (Term term : items) {
            // TODO (AndreiS): fix KItem projection
            if (!(term instanceof Variable) && !(term instanceof KItemProjection) && (term.kind() == kind)) {
                assert term instanceof KList :
                    "associative use of KList(" + items + ", " + frame + ")";

                KList kList = (KList) term;
    
                assert !kList.hasFrame() : "associative use of KCollection";
    
                normalizedItemsBuilder.addAll(kList.contents);
            } else {
                normalizedItemsBuilder.add(term);
            }
        }
        this.contents = normalizedItemsBuilder.build();
    }

    public KList(List<Term> items) {
        this(items, null);
    }

    public KList(Variable frame) {
        super(frame, Kind.KLIST);
        this.contents = ImmutableList.of();
    }
    
    /**
     * Private constructor only used for building KList fragment.
     * @param contents
     * @param frame
     */
    private KList(ImmutableList<Term> contents, Variable frame) {
        super(frame, Kind.KLIST);
        this.contents = contents;
    }

    @Override
    public KCollection fragment(int fromIndex) {
        return new KList(contents.subList(fromIndex, contents.size()), frame);
    }

    @Override
    public List<Term> getContents() {
        return contents;
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
        return KList.SEPARATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KList.IDENTITY_NAME;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KList)) {
            return false;
        }

        KList kList = (KList) object;
        return (frame == null ? kList.frame == null : frame.equals(kList.frame))
                && contents.equals(kList.contents);
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
