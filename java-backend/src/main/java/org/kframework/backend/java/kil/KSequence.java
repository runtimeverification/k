// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.apache.commons.collections4.ListUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kore.K;

import java.util.Collections;
import java.util.List;


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
public class KSequence extends KCollection implements org.kframework.kore.KSequence {

    private static final String SEPARATOR_NAME = " ~> ";
    private static final String IDENTITY_NAME = "." + Kind.K;
    public static final KSequence EMPTY = new KSequence(ImmutableList.<Term>of(), null, ImmutableList.<Variable>of());

    private final ImmutableList<Term> contents;

    /**
     * List of variables of sort K in {@link KSequence#contents}.
     */
    private final ImmutableList<Variable> kSequenceVariables;

    /**
     * Builds a KSequence consisting of the given variable. This method is
     * necessary in addition to the {@code Builder} because the {@code Builder}
     * will canonicalize its result and, thus, simply return the given variable.
     */
    public static KSequence frame(Variable variable) {
        assert variable.kind().equals(Kind.K);
        return new KSequence(ImmutableList.of(), variable, ImmutableList.<Variable>of());
    }

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
     * Splits the content and the frame variable of a potentially canonicalized
     * {@code KSequence}.
     */
    public static Pair<Term, Variable> splitContentAndFrame(Term term) {
        if (term instanceof Variable && term.sort().equals(Sort.KSEQUENCE)) {
            return Pair.of(EMPTY, (Variable) term);
        } else if (term.kind() == Kind.KITEM) {
            return Pair.of(term, null);
        } else if (term instanceof KSequence) {
            KSequence kSequence = (KSequence) term;
            Builder builder = builder();
            kSequence.contents.forEach(builder::concatenate);
            return Pair.of(builder.build(), kSequence.frame);
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
    public List<K> items() {
        if (frame != null) {
            return ListUtils.union(super.items(), Collections.singletonList(frame));
        } else {
            return super.items();
        }
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
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
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
