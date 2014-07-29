// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.apache.commons.lang3.mutable.MutableInt;
import org.kframework.backend.java.indexing.ConfigurationTermIndex;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.CopyOnShareSubstAndEvalTransformer;
import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.symbolic.Matchable;
import org.kframework.backend.java.symbolic.SubstituteAndEvaluateTransformer;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.Unifiable;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.loader.Constants;
import org.kframework.utils.general.IndexingStatistics;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject implements Transformable, Matchable, Unifiable, Comparable<Term> {

    protected final Kind kind;
    // protected final boolean normalized;

    private Boolean hasCell = null;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * Translates a term from the generic KIL representation ({@link org.kframework.kil.Term}) to
     * Java Rewrite Engine internal representation ({@link org.kframework.backend.java.kil.Term}).
     */
    public static Term of(org.kframework.kil.Term kilTerm, Definition definition) {
        if (definition.context().javaExecutionOptions.indexingStats){
            IndexingStatistics.kilTransformationStopWatch.start();
        }

        KILtoBackendJavaKILTransformer transformer
                = new KILtoBackendJavaKILTransformer(definition.context());
        Term term = transformer.transformTerm(kilTerm, definition);

        if (definition.context().javaExecutionOptions.indexingStats){
            IndexingStatistics.kilTransformationStopWatch.stop();
        }
        return term;
    }

    /**
     * Returns a {@link List} view of the indexing pairs from the {@code k}
     * cells of this {@code Term}.
     */
    public List<IndexingPair> getKCellIndexingPairs(final Definition definition) {
        final List<IndexingPair> indexingPairs = new ArrayList<IndexingPair>();
        accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                if (cell.getLabel().equals("k")) {
                    indexingPairs.add(IndexingPair.getKCellIndexingPair(cell, definition));
                } else if (cell.contentKind() == Kind.CELL_COLLECTION) {
                    super.visit(cell);
                }
            }
        });
        return indexingPairs;
    }

    public ConfigurationTermIndex getConfigurationTermIndex(final Definition definition) {
        final List<IndexingPair> kCellIndexingPairs = new ArrayList<>();
        final List<IndexingPair> instreamIndexingPairs = new ArrayList<>();
        final List<IndexingPair> outstreamIndexingPairs = new ArrayList<>();
        final MutableInt maxInputBufLen = new MutableInt(-1);
        final MutableInt maxOutputBufLen = new MutableInt(-1);
        accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                String cellLabel = cell.getLabel();
                String streamCellAttr = definition.context().getConfigurationStructureMap().get(cellLabel).cell.getCellAttribute("stream");
                if (cellLabel.equals("k")) {
                    kCellIndexingPairs.add(IndexingPair.getKCellIndexingPair(cell, definition));
                } else if (Constants.STDIN.equals(streamCellAttr)) {
                    BuiltinList instream = (BuiltinList) cell.getContent();
                    instreamIndexingPairs.add(IndexingPair.getInstreamIndexingPair(instream, definition));
                    maxInputBufLen.setValue(Math.max(maxInputBufLen.intValue(), instream.size()));
                } else if (Constants.STDOUT.equals(streamCellAttr) || Constants.STDERR.equals(streamCellAttr)) {
                    BuiltinList outstream = (BuiltinList) cell.getContent();
                    outstreamIndexingPairs.add(IndexingPair.getOutstreamIndexingPair(outstream, definition));
                    maxOutputBufLen.setValue(Math.max(maxOutputBufLen.intValue(), outstream.size()));
                } else if (cell.contentKind() == Kind.CELL_COLLECTION) {
                    super.visit(cell);
                }
            }
        });
        return new ConfigurationTermIndex(kCellIndexingPairs,
                instreamIndexingPairs, outstreamIndexingPairs,
                maxInputBufLen.intValue(), maxOutputBufLen.intValue());
    }

    /**
     * Returns true if this term has exactly the sort returned by {@link #sort()},
     * and not any of its proper subsorts.
     *
     * @see #sort()
     */
    public abstract boolean isExactSort();

    /**
     * Returns {@code true} if a unification task between this term and another term cannot be
     * further decomposed into simpler unification tasks.
     */
    public abstract boolean isSymbolic();

    /**
     * Returns the kind of this term (Cell, CellCollection, KItem, K, KLabel, KList, or Map).
     */
    public Kind kind() {
        return kind;
    }

    public abstract Sort sort();

    /**
     * @return {@code true} if this term has {@code Cell} inside; otherwise,
     *         {@code false}
     */
    public final boolean hasCell() {
        if (hasCell == null) {
            hasCell = computeHasCell();
        }
        return hasCell;
    }

    /**
     * Checks if this term has {@code Cell} inside.
     */
    protected abstract boolean computeHasCell();

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating
     * pending functions and predicates. <br>
     * TODO(YilongL): gradually eliminate the use of this method and switch to
     * the one with constraint, i.e., {@link this#evaluate(SymbolicConstraint,
     * TermContext)}.
     */
    public Term evaluate(TermContext context) {
        return evaluate(null, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating
     * pending functions and predicates.
     * <p>
     * This method carries a symbolic constraint as argument for two reasons: 1)
     * at the time when this method is called, the symbolic constraint
     * associated with the outer constrained term which contains this term may
     * not been properly simplified and normalized, which means the evaluation
     * process may still need the information of this constraint when performing
     * unification; 2) the evaluation process may create new constraints in
     * certain cases (e.g., in test generation).
     *
     * @param constraint
     *            the symbolic constraint of the {@link ConstrainedTerm} which
     *            contains this {@code Term}
     * @param context
     *            the term context
     * @return the result {@code Term} instance
     */
    public Term evaluate(SymbolicConstraint constraint, TermContext context) {
        return Evaluator.evaluate(this, constraint, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying a binder insensitive substitution.
     */
    @Override
    public Term substitute(Map<Variable, ? extends Term> substitution, TermContext context) {
        return (Term) super.substitute(substitution, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying a binder-aware substitution.
     */
    @Override
    public Term substituteWithBinders(Map<Variable, ? extends Term> substitution, TermContext context) {
        return (Term) super.substituteWithBinders(substitution, context);
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying
     * substitution.
     * <p>
     * Note: for efficiency reason, this method will only evaluate functions
     * that become concrete due to the substitution. That is to say, concrete
     * pending functions are omitted by this method. In this case, use the
     * {@code evaluate} method instead.
     */
    public Term substituteAndEvaluate(Map<Variable, ? extends Term> substitution, TermContext context) {
        // TODO(AndreiS): assert that there are not any unevaluated functions in this term
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        // YilongL: comment out the slow implementation
//        SubstitutionTransformer transformer = new BinderSubstitutionTransformer(substitution, context);
//        transformer.getPostTransformer().addTransformer(new LocalEvaluator(context));
//        return (Term) accept(transformer);
        SubstituteAndEvaluateTransformer transformer = new SubstituteAndEvaluateTransformer(substitution, context);
        return (Term) this.accept(transformer);
    }

    /**
     * Similar to {@link Term#substituteAndEvaluate(Map, TermContext)} except
     * that this method will copy the terms used for substitution whenever
     * necessary in order to avoid undesired sharing of mutable terms.
     *
     * @param substitution
     *            the substitution map; TODO(YilongL): this may become a
     *            multi-map in the future when the pattern matching algorithm
     *            allows us to record multiple equal terms binding to a variable
     *            for the sake of maximizing term reuse
     * @param variablesToReuse
     *            a set of variables in the substitution whose binding terms can
     *            be reused to build the new term
     * @param context
     * @return a new term obtained by applying substitution
     */
    public Term copyOnShareSubstAndEval(
            Map<Variable, ? extends Term> substitution,
            Set<Variable> variablesToReuse, TermContext context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }
        CopyOnShareSubstAndEvalTransformer transformer = new CopyOnShareSubstAndEvalTransformer(
                substitution, variablesToReuse, context);
        return (Term) this.accept(transformer);
    }

     /**
     * Returns a new {@code Term} instance obtained from this term by substituting variable with
     * term.
     */
    @Override
    public Term substituteWithBinders(Variable variable, Term term, TermContext context) {
        return (Term) super.substituteWithBinders(variable, term, context);
    }

    @Override
    public final int compareTo(Term o) {
        return toString().compareTo(o.toString());
    }

    /**
     * Computes and caches the hashCode if it has not been computed yet.
     * Otherwise, simply returns the cached value.
     */
    @Override
    public final int hashCode() {
        if (hashCode == Utils.NO_HASHCODE) {
            hashCode = computeHash();
            hashCode = hashCode == 0 ? 1 : hashCode;
        }
        return hashCode;
    }

    /**
     * (Re-)computes the hashCode of this {@code Term}.
     * @return the hash code
     */
    protected abstract int computeHash();

    @Override
    public abstract boolean equals(Object object);
}
