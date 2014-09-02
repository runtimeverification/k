// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.List;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableList;


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
    public static final KSequence EMPTY = (KSequence) builder().build();

    private final ImmutableList<Term> contents;

    public static KSequence singleton(Term term) {
        assert term.kind().equals(Kind.KITEM);
        return new KSequence(ImmutableList.of(term), null);
    }

    private KSequence(ImmutableList<Term> contents, Variable frame) {
        super(frame, Kind.K);
        this.contents = contents;
    }

    @Override
    public Term fragment(int fromIndex) {
        if (fromIndex == contents.size()) {
            return hasFrame() ? frame : EMPTY;
        } else {
            return new KSequence(contents.subList(fromIndex, contents.size()), frame);
        }
    }

    @Override
    public List<Term> getContents() {
        return contents;
    }

    @Override
    public Sort sort() {
        return !hasFrame() && concreteSize() == 1 ? contents.get(0).sort() : Sort.KSEQUENCE;
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

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {

        private final ImmutableList.Builder<Term> builder = ImmutableList.builder();

        public void concatenate(Term term) {
            if (term instanceof KSequence) {
                KSequence kseq = (KSequence) term;
                builder.addAll(kseq.contents);
                if (kseq.hasFrame()) {
                    builder.add(kseq.frame);
                }
            } else if (term instanceof Variable) {
                assert term.sort().equals(Sort.KSEQUENCE) || term.kind().equals(Kind.KITEM);
                builder.add(term);
            } else if (term.kind().equals(Kind.KITEM)) {
                builder.add(term);
            } else if (term instanceof KItemProjection) {
                // TODO(AndreiS): fix KItem projection
                builder.add(term);
            } else {
                assert false : "unexpected concatenated term" + term;
            }
        }

        public Term build() {
            ImmutableList<Term> contents = builder.build();
            Variable frame = null;
            if (!contents.isEmpty()) {
                Term lastElem = contents.get(contents.size() - 1);
                if (lastElem instanceof Variable && lastElem.kind().equals(Kind.K)) {
                    frame = (Variable) lastElem;
                    contents = contents.subList(0, contents.size() - 1);
                }
            }

            if (contents.isEmpty() && frame != null) {
                return frame;
            } else if (contents.size() == 1 && frame == null) {
                return contents.get(0);
            } else {
                return new KSequence(contents, frame);
            }
        }
    }

}
