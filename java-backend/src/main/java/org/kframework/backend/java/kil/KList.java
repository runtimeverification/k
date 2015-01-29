// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.List;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
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
public class KList extends KCollection {

    private static final String SEPARATOR_NAME = ",, ";
    private static final String IDENTITY_NAME = "." + Kind.KLIST;
    public static final KList EMPTY = new KList(ImmutableList.<Term>of(), null, ImmutableList.<Variable>of());

    /**
     * A list of {@code Term}s contained in this {@code KList}.
     */
    private final ImmutableList<Term> contents;

    /**
     * List of variables of sort KList in {@link KList#contents}.
     */
    private final ImmutableList<Variable> kListVariables;

    /**
     * Builds a single-element KList based on the given term. This method is
     * necessary in addition to the {@code Builder} because the {@code Builder}
     * will canonicalize its result and, thus, simply return the given term.
     */
    public static KList singleton(Term term) {
        assert term.kind().equals(Kind.K) || term.kind.equals(Kind.KITEM);
        return new KList(ImmutableList.of(term), null, ImmutableList.<Variable>of());
    }

    public static Term concatenate(Term... terms) {
        Builder builder = builder();
        for (Term term : terms) {
            builder.concatenate(term);
        }
        return builder.build();
    }

    public static Term concatenate(List<Term> terms) {
        Builder builder = builder();
        for (Term term : terms) {
            builder.concatenate(term);
        }
        return builder.build();
    }

    private KList(ImmutableList<Term> contents, Variable frame, ImmutableList<Variable> kListVariables) {
        super(frame, Kind.KLIST);
        this.contents = contents;
        this.kListVariables = kListVariables;
    }

    @Override
    public Term fragment(int fromIndex) {
        if (fromIndex == contents.size()) {
            return hasFrame() ? frame : EMPTY;
        } else {
            if (kListVariables.isEmpty()) {
                return fromIndex + 1 == contents.size() ?
                        contents.get(fromIndex) :
                        new KList(contents.subList(fromIndex, contents.size()), frame, kListVariables);
            } else {
                /* YilongL: this case should never happen in practice because
                 * this method should only be called by KList on the LHS */
                int idx = 0;
                for (int i = 0; i < fromIndex; i++) {
                    if (contents.get(i) == kListVariables.get(idx)) {
                        idx++;
                    }
                }
                return new KList(contents.subList(fromIndex, contents.size()),
                        frame, kListVariables.subList(idx, kListVariables.size()));
            }
        }
    }

    @Override
    public List<Term> getContents() {
        return contents;
    }

    @Override
    public ImmutableList<Variable> collectionVariables() {
        return kListVariables;
    }

    @Override
    public final boolean isConcreteCollection() {
        return kListVariables.isEmpty();
    }

    @Override
    public Sort sort() {
        return concreteSize() == 1 && !hasFrame() ? contents.get(0).sort() : Sort.KLIST;
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

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {

        private final ImmutableList.Builder<Term> contentsBuilder = ImmutableList.builder();

        private final ImmutableList.Builder<Variable> variablesBuilder = ImmutableList.builder();

        private Variable frame = null;

        public void concatenate(Term term) {
            if (frame != null && !term.equals(EMPTY)) {
                contentsBuilder.add(frame);
                variablesBuilder.add(frame);
                frame = null;
            }

            if (term instanceof KList) {
                KList kList = (KList) term;
                contentsBuilder.addAll(kList.contents);
                frame = kList.frame;
            } else if (term instanceof Variable) {
                assert term.sort().equals(Sort.KLIST) || term.kind().equals(Kind.KITEM) || term.kind().equals(Kind.K);
                if (term.sort().equals(Sort.KLIST)) {
                    frame = (Variable) term;
                } else {
                    contentsBuilder.add(term);
                }
            } else if (term.kind().equals(Kind.KITEM) || term.kind().equals(Kind.K)) {
                contentsBuilder.add(term);
            } else if (term instanceof KItemProjection) {
                // TODO(AndreiS): fix KItem projection
                contentsBuilder.add(term);
            } else {
                assert false : "unexpected concatenated term" + term;
            }
        }

        /**
         * Returns a newly-created canonicalized KList based on the contents of the builder.
         */
        public Term build() {
            ImmutableList<Term> contents = contentsBuilder.build();
            if (frame != null) {
                variablesBuilder.add(frame);
            }

            if (contents.isEmpty()) {
                return frame == null ? EMPTY : frame;
            } else if (contents.size() == 1 && frame == null) {
                return contents.get(0);
            } else {
                return new KList(contents, frame, variablesBuilder.build());
            }
        }

    }

}
