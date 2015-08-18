// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import com.google.inject.Provider;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.JavaKRunState;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.RewriteRelation;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.tools.Executor;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class JavaSymbolicExecutor implements Executor {

    private final JavaExecutionOptions javaOptions;
    private final KILtoBackendJavaKILTransformer kilTransformer;
    private final GlobalContext globalContext;
    private final Provider<SymbolicRewriter> symbolicRewriter;
    private final Provider<PatternMatchRewriter> patternMatchRewriter;
    private final KILtoBackendJavaKILTransformer transformer;
    private final Context context;
    private final KRunState.Counter counter;
    private final Stopwatch sw;

    @Inject
    JavaSymbolicExecutor(
            Context context,
            JavaExecutionOptions javaOptions,
            KILtoBackendJavaKILTransformer kilTransformer,
            GlobalContext globalContext,
            Provider<SymbolicRewriter> symbolicRewriter,
            Provider<PatternMatchRewriter> patternMatchRewriter,
            KILtoBackendJavaKILTransformer transformer,
            Definition definition,
            KRunState.Counter counter,
            Stopwatch sw) {
        this.context = context;
        this.javaOptions = javaOptions;
        this.kilTransformer = kilTransformer;
        this.globalContext = globalContext;
        this.symbolicRewriter = symbolicRewriter;
        this.patternMatchRewriter = patternMatchRewriter;
        this.transformer = transformer;
        globalContext.setDefinition(definition);
        this.counter = counter;
        this.sw = sw;
    }

    @Override
    public RewriteRelation run(org.kframework.kil.Term cfg, boolean computeGraph) throws KRunExecutionException {
        return javaRewriteEngineRun(cfg, -1, computeGraph);
    }

    /**
     * private method to convert a generic kil term to java kil.1
     *
     * @return JavaKil Term.
     */
    private Term getJavaKilTerm(org.kframework.kil.Term cfg) {
        Term term = kilTransformer.transformAndEval(cfg);
        sw.printIntermediate("Convert initial configuration to internal representation");
        TermContext termContext = TermContext.of(globalContext);
        termContext.setTopTerm(term);
        return term;
    }

    /**
     * Given a term, return the TermContext constructed from the globalContext
     *
     * @param term
     * @return
     */
    private TermContext getTermContext(Term term) {
        TermContext termContext = TermContext.of(globalContext);
        termContext.setTopTerm(term);
        return termContext;
    }


    private RewriteRelation patternMatcherRewriteRun(Term term, TermContext termContext, int bound, boolean computeGraph) {

        if (computeGraph) {
            KEMException.criticalError("Compute Graph with Pattern Matching Not Implemented Yet");
        }
        ConstrainedTerm rewriteResult = new ConstrainedTerm(getPatternMatchRewriter().rewrite(term, bound, termContext), termContext);
        JavaKRunState finalState = new JavaKRunState(rewriteResult, context, counter);
        return new RewriteRelation(finalState, null);
    }

    private RewriteRelation conventionalRewriteRun(ConstrainedTerm constrainedTerm, int bound, boolean computeGraph) {
        SymbolicRewriter rewriter = symbolicRewriter.get();
        KRunState finalState = rewriter.rewrite(
                constrainedTerm,
                context,
                bound,
                computeGraph);

        return new RewriteRelation(finalState, rewriter.getExecutionGraph());
    }

    /**
     * Rewrite Enginre run that creates a new KRun State.
     * @param cfg The term configuration to begin with.
     * @param bound The number of steps
     * @param computeGraph Option to compute Execution Graph,
     * @return The execution relation.
     */
    private RewriteRelation javaRewriteEngineRun(org.kframework.kil.Term cfg, int bound, boolean computeGraph) {
        Term term = getJavaKilTerm(cfg);
        TermContext termContext = getTermContext(term);
        if (!javaOptions.symbolicExecution) {
            return patternMatcherRewriteRun(term, termContext, bound, computeGraph);
        }
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(term, ConjunctiveFormula.of(termContext));
        return conventionalRewriteRun(constrainedTerm, bound, computeGraph);
    }

    /**
     * Rewrite Engine Run with existing krun State.
     * @param initialState The existing State
     * @param bound The number of steps
     * @param computeGraph Option to compute Execution Graph.
     * @return The execution relation.
     */
    private RewriteRelation javaRewriteEngineRun(JavaKRunState initialState, int bound, boolean computeGraph) {
        return conventionalRewriteRun(initialState.getConstrainedTerm(), bound, computeGraph);
    }


    @Override
    public SearchResults search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo,
            boolean computeGraph) throws KRunExecutionException {

        List<Rule> claims = Collections.emptyList();
        if (bound == null) {
            bound = -1;
        }
        if (depth == null) {
            depth = -1;
        }

        // The pattern needs to be a rewrite in order for the transformer to be
        // able to handle it, so we need to give it a right-hand-side.
        org.kframework.kil.Cell c = new org.kframework.kil.Cell();
        c.setLabel("generatedTop");
        c.setContents(new org.kframework.kil.Bag());
        pattern.setBody(new org.kframework.kil.Rewrite(pattern.getBody(), c, context));
        Rule patternRule = transformer.transformAndEval(pattern);

        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<Substitution<Variable, Term>> hits;
        Term initialTerm = kilTransformer.transformAndEval(cfg);
        Term targetTerm = null;
        TermContext termContext = TermContext.of(globalContext);
        KRunGraph executionGraph = null;
        if (!javaOptions.symbolicExecution) {
            if (computeGraph) {
                KEMException.criticalError("Compute Graph with Pattern Matching Not Implemented Yet");
            }
            hits = getPatternMatchRewriter().search(initialTerm, targetTerm, claims,
                    patternRule, bound, depth, searchType, termContext);
        } else {
            SymbolicRewriter rewriter = getSymbolicRewriter();
            hits = rewriter.search(initialTerm, targetTerm, claims,
                    patternRule, bound, depth, searchType, termContext, computeGraph);
            executionGraph = rewriter.getExecutionGraph();
        }

        for (Map<Variable, Term> map : hits) {
            // Construct substitution map from the search results
            Map<String, org.kframework.kil.Term> substitutionMap =
                    new HashMap<String, org.kframework.kil.Term>();
            for (Variable var : map.keySet()) {
                org.kframework.kil.Term kilTerm =
                        (org.kframework.kil.Term) map.get(var).accept(
                                new BackendJavaKILtoKILTransformer(context));
                substitutionMap.put(var.name(), kilTerm);
            }

            // Apply the substitution to the pattern
            org.kframework.kil.Term rawResult =
                    (org.kframework.kil.Term) new SubstitutionFilter(substitutionMap, context)
                            .visitNode(pattern.getBody());

            searchResults.add(new SearchResult(
                    new JavaKRunState(rawResult, counter),
                    substitutionMap,
                    compilationInfo));
        }

        SearchResults retval = new SearchResults(
                searchResults,
                executionGraph);

        return retval;
    }

    @Override
    public RewriteRelation step(org.kframework.kil.Term cfg, int steps, boolean computeGraph)
            throws KRunExecutionException {
        return javaRewriteEngineRun(cfg, steps, computeGraph);
    }

    public SymbolicRewriter getSymbolicRewriter() {
        return symbolicRewriter.get();
    }

    private PatternMatchRewriter getPatternMatchRewriter() {
        return patternMatchRewriter.get();
    }
}
