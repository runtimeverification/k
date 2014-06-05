// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.List;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
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
    private String sort;
    
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
        return new KSequence(items, (Variable) frame);
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
                assert term instanceof KSequence :
                    "associative use of KSequence(" + items + ", " + frame + ")";

                KSequence kseq = (KSequence) term;
    
                assert !kseq.hasFrame() : "associative use of KSequence";

                if (stack.isEmpty()) {
                    stack = kseq.contents;
                } else {
                    stack = stack.plusAll(kseq.contents);
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
    
    /**
     * Serializes the {@link PStack} as a sequence of elements because it
     * doesn't properly implement {@link Serializable}.
     * 
     * @param out
     *            the output object stream
     * @throws IOException
     */
    private void writeObject(ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(contents.toArray());
    }
    
    /**
     * Deserializes this {@code KSequence} object. In particular, it rebuilds
     * the {@code contents} during deserialization.
     * 
     * @param in
     *            the input object stream
     * @throws IOException
     * @throws ClassNotFoundException
     * @throws IllegalArgumentException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws SecurityException
     */
    private void readObject(ObjectInputStream in) throws IOException,
            ClassNotFoundException, IllegalArgumentException,
            IllegalAccessException, NoSuchFieldException, SecurityException {
        in.defaultReadObject();

        Object[] termArray = (Object[]) in.readObject();
        PStack<Term> stack = ConsPStack.empty();
        for (int i = termArray.length - 1; i >= 0; i--) {
            stack = stack.plus((Term) termArray[i]);
        }
        Field f = KSequence.class.getDeclaredField("contents");
        f.setAccessible(true);
        f.set(this, stack);
    }
}
