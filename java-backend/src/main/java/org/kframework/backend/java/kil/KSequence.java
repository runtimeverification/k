// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
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
    public static final KSequence EMPTY = new KSequence(ImmutableList.<Term>of(), null, ImmutableList.<Variable>of());

    private final ImmutableList<Term> contents;

    /**
     * List of variables of sort K in {@link KSequence#contents}.
     */
    private final ImmutableList<Variable> kSequenceVariables;

    /**
     * Builds a single-element KSequence based on the given term. This method is
     * necessary in addition to the {@code Builder} because the {@code Builder}
     * will canonicalize its result and, thus, simply return the given term.
     */
    public static KSequence singleton(Term term) {
        assert term.kind().equals(Kind.KITEM);
        return new KSequence(ImmutableList.of(term), null, ImmutableList.<Variable>of());
    }

    /**
     * Retrieves the frame variable of a given term representing a potentially
     * canonicalized {@code KSequence}.
     */
    public static Variable getFrame(Term term) {
        if (term instanceof Variable && term.sort().equals(Sort.KSEQUENCE)) {
            return (Variable) term;
        } else if (term.kind() == Kind.KITEM) {
            return null;
        } else if (term instanceof KSequence) {
            return ((KSequence) term).frame;
        } else {
            assert false : "unexpected argument: " + term;
            return null;
        }
    }

    /**
     * Retrieves the list of elements of a given term representing a potentially
     * canonicalized {@code KSequence}.
     */
    public static List<Term> getElements(Term term) {
        if (term instanceof Variable && term.sort().equals(Sort.KSEQUENCE)) {
            return Collections.emptyList();
        } else if (term.kind() == Kind.KITEM) {
            return Collections.singletonList(term);
        } else if (term instanceof KSequence) {
            return ((KSequence) term).contents;
        } else {
            assert false : "unexpected argument: " + term;
            return null;
        }
    }

    private KSequence(ImmutableList<Term> contents, Variable frame, ImmutableList<Variable> kSequenceVariables) {
        super(frame, Kind.K);
        this.contents = contents;
        this.kSequenceVariables = kSequenceVariables;
    }

    @Override
    public Term fragment(int fromIndex) {
        if (fromIndex == contents.size()) {
            return hasFrame() ? frame : EMPTY;
        } else {
            if (kSequenceVariables.isEmpty()) {
                return fromIndex + 1 == contents.size() ?
                        contents.get(fromIndex) :
                        new KSequence(contents.subList(fromIndex, contents.size()), frame, kSequenceVariables);
            } else {
                /* YilongL: this case should never happen in practice because
                 * this method should only be called by KSequence on the LHS */
                int idx = 0;
                for (int i = 0; i < fromIndex; i++) {
                    if (contents.get(i) == kSequenceVariables.get(idx)) {
                        idx++;
                    }
                }
                return new KSequence(contents.subList(fromIndex, contents.size()),
                        frame, kSequenceVariables.subList(idx, kSequenceVariables.size()));
            }
        }
    }

    @Override
    public List<Term> getContents() {
        return contents;
    }

    @Override
    public ImmutableList<Variable> collectionVariables() {
        return kSequenceVariables;
    }

    @Override
    public final boolean isConcreteCollection() {
        return kSequenceVariables.isEmpty();
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

        private final ImmutableList.Builder<Term> contentsBuilder = ImmutableList.builder();
        private final ImmutableList.Builder<Variable> variablesBuilder = ImmutableList.builder();
        private Variable frame = null;

        public void concatenate(Term term) {
            if (frame != null && !term.equals(EMPTY)) {
                contentsBuilder.add(frame);
                variablesBuilder.add(frame);
                frame = null;
            }

            if (term instanceof KSequence) {
                KSequence kseq = (KSequence) term;
                contentsBuilder.addAll(kseq.contents);
                frame = kseq.frame;
            } else if (term instanceof Variable) {
                assert term.sort().equals(Sort.KSEQUENCE) || term.kind().equals(Kind.KITEM);
                if (term.sort().equals(Sort.KSEQUENCE)) {
                    frame = (Variable) term;
                } else {
                    contentsBuilder.add(term);
                }
            } else if (term.kind().equals(Kind.KITEM)) {
                contentsBuilder.add(term);
            } else if (term instanceof KItemProjection) {
                // TODO(AndreiS): fix KItem projection
                contentsBuilder.add(term);
            } else {
                assert false : "unexpected concatenated term" + term;
            }
        }

        /**
         * Returns a newly-created canonicalized KSequence based on the contents of the builder.
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
                return new KSequence(contents, frame, variablesBuilder.build());
            }
        }
    }

}
