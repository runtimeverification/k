// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.transformers.DataStructureToLookupUpdate;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.ConfigurationSubstitutionVisitor;
import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.krun.KRunOptions.OutputMode;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.Transition;
import org.kframework.krun.api.UnsupportedBackendOptionException;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import edu.uci.ics.jung.graph.DirectedGraph;

import org.kframework.utils.general.IndexingStatistics;

import com.google.inject.Inject;
import com.google.inject.Provider;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 *
 *
 * @author AndreiS
 */
public class JavaSymbolicKRun implements KRun {

    private final Definition definition;
    private final Context context;
    private final JavaExecutionOptions options;
    private final KILtoBackendJavaKILTransformer transformer;
    private final Provider<SymbolicRewriter> symbolicRewriter;
    private final KilFactory kilFactory;
    private final GlobalContext globalContext;

    @Inject
    JavaSymbolicKRun(
            Context context,
            Definition definition,
            JavaExecutionOptions options,
            Provider<SymbolicRewriter> symbolicRewriter,
            KilFactory kilFactory,
            GlobalContext globalContext,
            KILtoBackendJavaKILTransformer transformer) {
        this.definition = definition;
        this.context = context;
        this.options = options;
        this.symbolicRewriter = symbolicRewriter;
        this.kilFactory = kilFactory;
        this.globalContext = globalContext;
        this.transformer = transformer;
        globalContext.setDefinition(definition);
    }

    public Definition getDefinition(){
        return this.definition;
    }

    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {
        if (options.indexingStats){
            IndexingStatistics.totalKrunStopwatch.start();
            KRunResult<KRunState> result = internalRun(cfg, -1);
            IndexingStatistics.totalKrunStopwatch.stop();
            IndexingStatistics.print();
            return result;
        } else{
            return internalRun(cfg, -1);
        }
    }

    private KRunResult<KRunState> internalRun(org.kframework.kil.Term cfg, int bound) throws KRunExecutionException {
        ConstrainedTerm result = javaKILRun(cfg, bound);
        org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                new BackendJavaKILtoKILTransformer(context));
        KRunResult<KRunState> returnResult = new KRunResult<KRunState>(new KRunState(kilTerm, context), context);
        UnparserFilter unparser = new UnparserFilter(true, ColorSetting.OFF, OutputMode.PRETTY, context);
        unparser.visitNode(kilTerm);
        returnResult.setRawOutput(unparser.getResult());
        return returnResult;
    }

    private ConstrainedTerm javaKILRun(org.kframework.kil.Term cfg, int bound) {
        if (options.indexingStats){
            IndexingStatistics.preProcessStopWatch.start();
        }

        Term term = kilFactory.term(cfg);
        TermContext termContext = TermContext.of(globalContext);
        term = term.evaluate(termContext);

        if (options.patternMatching) {
            FastDestructiveRewriter rewriter = new FastDestructiveRewriter(definition, termContext);
            ConstrainedTerm rewriteResult = new ConstrainedTerm(rewriter.rewrite(term, bound), termContext);
            return rewriteResult;
        } else {
            SymbolicConstraint constraint = new SymbolicConstraint(termContext);
            ConstrainedTerm constrainedTerm = new ConstrainedTerm(term, constraint, termContext);
            if (options.indexingStats){
                IndexingStatistics.preProcessStopWatch.stop();
            }
            ConstrainedTerm rewriteResult;
            if (options.indexingStats) {
                IndexingStatistics.totalRewriteStopwatch.start();
                rewriteResult = symbolicRewriter.get().rewrite(constrainedTerm, bound);
                IndexingStatistics.totalRewriteStopwatch.stop();
            } else {
                rewriteResult = symbolicRewriter.get().rewrite(constrainedTerm, bound);
            }
            return rewriteResult;
        }
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(Module module, org.kframework.kil.Term cfg) throws KRunExecutionException {
        TermContext termContext = TermContext.of(globalContext);
        Map<org.kframework.kil.Term, org.kframework.kil.Term> substitution = null;
        if (cfg != null) {
            cfg = run(cfg).getResult().getRawResult();
            ConfigurationSubstitutionVisitor configurationSubstitutionVisitor =
                    new ConfigurationSubstitutionVisitor(context);
            configurationSubstitutionVisitor.visitNode(cfg);
            substitution = configurationSubstitutionVisitor.getSubstitution();
//            System.out.println(substitution);
            Module mod = module;
            mod = (Module) new Substitution(substitution,context).visitNode(module);
//                System.out.println(mod.toString());
            module = mod;
        }
        try {
            module = new SpecificationCompilerSteps(context).compile(module, null);
        } catch (CompilerStepDone e) {
            assert false: "dead code";
        }
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();

        DataStructureToLookupUpdate mapTransformer = new DataStructureToLookupUpdate(context);

        List<Rule> rules = new ArrayList<Rule>();
        for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
            if (!(moduleItem instanceof org.kframework.kil.Rule)) {
                continue;
            }

            Rule rule = transformer.transformRule(
                    (org.kframework.kil.Rule) mapTransformer.visitNode(moduleItem));
            Rule freshRule = rule.getFreshRule(termContext);
            rules.add(freshRule);
        }

        SymbolicRewriter symbolicRewriter = this.symbolicRewriter.get();
        for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
            if (!(moduleItem instanceof org.kframework.kil.Rule)) {
                continue;
            }

            org.kframework.kil.Rule kilRule = (org.kframework.kil.Rule) moduleItem;
            org.kframework.kil.Term kilLeftHandSide
                    = ((org.kframework.kil.Rewrite) kilRule.getBody()).getLeft();
            org.kframework.kil.Term kilRightHandSide =
                    ((org.kframework.kil.Rewrite) kilRule.getBody()).getRight();
            org.kframework.kil.Term kilRequires = kilRule.getRequires();
            org.kframework.kil.Term kilEnsures = kilRule.getEnsures();

            org.kframework.kil.Rule kilDummyRule = new org.kframework.kil.Rule(
                    kilRightHandSide,
                    MetaK.kWrap(org.kframework.kil.KSequence.EMPTY, "k"),
                    kilRequires,
                    kilEnsures,
                    context);
            Rule dummyRule = transformer.transformRule(
                    (org.kframework.kil.Rule) mapTransformer.visitNode(kilDummyRule));

            SymbolicConstraint initialConstraint = new SymbolicConstraint(termContext);
            initialConstraint.addAll(dummyRule.requires());
            ConstrainedTerm initialTerm = new ConstrainedTerm(
                    transformer.transformTerm(kilLeftHandSide, definition),
                    initialConstraint,
                    termContext);

            SymbolicConstraint targetConstraint = new SymbolicConstraint(termContext);
            targetConstraint.addAll(dummyRule.ensures());
            ConstrainedTerm targetTerm = new ConstrainedTerm(
                    dummyRule.leftHandSide().evaluate(termContext),
                    dummyRule.lookups().getSymbolicConstraint(termContext),
                    targetConstraint,
                    termContext);

            proofResults.addAll(symbolicRewriter.proveRule(initialTerm, targetTerm, rules));
        }

        System.err.println(proofResults.isEmpty());
        System.err.println(proofResults);

        return new KRunProofResult<Set<org.kframework.kil.Term>>(
                proofResults.isEmpty(), Collections.<org.kframework.kil.Term>emptySet(), context);
    }

    @Override
    public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {

        if (options.indexingStats){
            IndexingStatistics.totalSearchStopwatch.start();
        }

        FileSystem fs = new PortableFileSystem();

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
        Rule patternRule = transformer.transformRule(pattern);

        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<Map<Variable,Term>> hits;
        if (options.patternMatching) {
            Term initialTerm = kilFactory.term(cfg);
            Term targetTerm = null;
            GroundRewriter rewriter = new GroundRewriter(definition, TermContext.of(globalContext));
            hits = rewriter.search(initialTerm, targetTerm, claims,
                    patternRule, bound, depth, searchType);
        } else {
            ConstrainedTerm initialTerm = new ConstrainedTerm(kilFactory.term(cfg), TermContext.of(globalContext));
            ConstrainedTerm targetTerm = null;
            hits = symbolicRewriter.get().search(initialTerm, targetTerm, claims,
                    patternRule, bound, depth, searchType);
        }

        for (Map<Variable,Term> map : hits) {
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
                    new KRunState(rawResult, context),
                    substitutionMap,
                    compilationInfo,
                    context));
        }

        // TODO(ericmikida): Make the isDefaultPattern option set in some reasonable way
        KRunResult<SearchResults> searchResultsKRunResult = new KRunResult<>(new SearchResults(
                searchResults,
                null,
                false,
                context), context);

        if (options.indexingStats){
            IndexingStatistics.totalSearchStopwatch.stop();
            IndexingStatistics.print();
        }
        return searchResultsKRunResult;
    }

    @Override
    public KRunResult<SearchResults> generate(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        throw new UnsupportedBackendOptionException("--test-gen");
    }

    @Override
    public KRunProofResult<DirectedGraph<KRunState, Transition>> modelCheck(
            org.kframework.kil.Term formula,
            org.kframework.kil.Term cfg) throws KRunExecutionException {
        throw new UnsupportedBackendOptionException("--ltlmc");
    }

    @Override
    public KRunResult<KRunState> step(org.kframework.kil.Term cfg, int steps)
            throws KRunExecutionException {
        return internalRun(cfg, steps);
    }

    @Override
    public KRunDebugger debug(org.kframework.kil.Term cfg) {
        throw new UnsupportedBackendOptionException("--debug");
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        throw new UnsupportedBackendOptionException("--debug");
    }

    @Override
    public void setBackendOption(String key, Object value) {
    }

}
