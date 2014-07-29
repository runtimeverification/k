// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.io.Serializable;
import java.util.List;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.pcollections.ConsPStack;
import org.pcollections.Empty;
import org.pcollections.PStack;

import com.google.common.collect.Lists;


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
    public static final KSequence EMPTY = new KSequence();

    /**
     * Marked as {@code transient} because {@code PStack} doesn't implement the
     * {@code Serializable} interface.
     */
    private transient final PStack<Term> contents;
    private Sort sort;

    /**
     * Concatenates a sequence of elements of sort K or KItem and a frame term.
     * <p>
     * Note: parameter {@code `List<Term> items'} can be modified by this
     * factory method; it is the caller's responsibility to make a defensive
     * copy when necessary.
     *
     * @param items
     * @param frame
     * @return the resulting K sequence
     */
    public static KSequence of(List<Term> items, Term frame) {
        if (frame != null) {
            if (frame.kind() == Kind.K) {
                if (frame instanceof KSequence) {
                    KSequence kseq = (KSequence) frame;
                    return new KSequence(items, new KSequence(kseq.contents, null), kseq.frame);
                } else {
                    // otherwise, frame must be a variable of sort K
                }
            } else {
                assert frame.kind() == Kind.KITEM;
                items.add(frame);
                frame = null;
            }
        }
        return new KSequence(items, null, (Variable) frame);
    }

    public KSequence(List<Term> items, Variable frame) {
        this(items, null, frame);
    }

    public KSequence(List<Term> items) {
        this(items, null, null);
    }

    private KSequence(List<Term> items, KSequence kSequence, Variable frame) {
        super(frame, Kind.K);

        assert kSequence == null || !kSequence.hasFrame();
        PStack<Term> stack = kSequence == null ? Empty.<Term>stack() : kSequence.contents;

        /* normalize (flatten) the items before creating the new KSequence */
        for (Term term : Lists.reverse(items)) {
            // TODO (AndreiS): fix KItem projection
            if (!(term instanceof Variable) && !(term instanceof KItemProjection) && (term.kind() == kind)) {
                // TODO(YilongL): the condition above seems hacky
                assert term instanceof KSequence :
                    "associative use of KSequence(" + items + ", " + frame + ")";

                KSequence kseq = (KSequence) term;

                assert !kseq.hasFrame() : "associative use of KSequence";

                if (stack.isEmpty()) {
                    stack = kseq.contents;
                } else {
                    stack = kseq.contents.size() <= 1 ?
                            stack.plusAll(kseq.contents) :
                            stack.plusAll(Lists.reverse(Lists.newArrayList(kseq.contents)));
                }
            } else {
                stack = stack.plus(term);
            }
        }
        this.contents = stack;
    }

    private KSequence() {
        super(null, Kind.K);
        contents = Empty.stack();
    }

    /**
     * Private constructor only used for building KSequence fragment.
     * @param contents
     * @param frame
     */
    private KSequence(PStack<Term> contents, Variable frame) {
        super(frame, Kind.K);
        this.contents = contents;
    }

    @Override
    public KSequence fragment(int fromIndex) {
        return new KSequence(contents.subList(fromIndex), frame);
    }

    @Override
    public PStack<Term> getContents() {
        return contents;
    }

    @Override
    public Sort sort() {
        if (sort != null) {
            return sort;
        }

        sort = size() == 1 && !hasFrame() ? contents.get(0).sort() : Sort.KSEQUENCE;
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

    /**
     * When this {@code KSequence} is being serialized, serialize its proxy
     * class instead.
     *
     * @return the serialization proxy of this {@code KSequence}
     */
    private Object writeReplace() {
        return new SerializationProxy(this);
    }

    private static class SerializationProxy implements Serializable {

        private List<Term> terms;
        private Variable frame;

        private SerializationProxy(KSequence kSequence) {
            /* converts the non-serializable PStack to normal list */
            this.terms = Lists.newArrayList(kSequence.contents);
            this.frame = kSequence.frame;
        }

        private Object readResolve() {
            PStack<Term> stack = ConsPStack.empty();
            for (Term term : Lists.reverse(terms)) {
                stack = stack.plus(term);
            }
            return new KSequence(stack, frame);
        }
    }
}
