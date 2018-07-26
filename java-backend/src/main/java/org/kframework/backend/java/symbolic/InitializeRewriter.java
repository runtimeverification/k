// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.HookProvider;
import org.kframework.backend.java.util.Profiler2;
import org.kframework.builtin.KLabels;
import org.kframework.compile.*;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;
import scala.Function1;
import scala.Tuple2;
import scala.collection.JavaConversions;

import java.lang.invoke.MethodHandle;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 5/6/15.
 */
public class InitializeRewriter implements Function<Module, Rewriter> {

    private final FileSystem fs;
    private final Stopwatch sw;
    private final GlobalOptions globalOptions;
    private final KExceptionManager kem;
    private final SMTOptions smtOptions;
    private final Map<String, MethodHandle> hookProvider;
    private final List<String> transitions;
    private final KRunOptions krunOptions;
    private final FileUtil files;
    private final InitializeDefinition initializeDefinition;
    private static final int NEGATIVE_VALUE = -1;
    private final KompileOptions kompileOptions;
    private final Profiler2 profiler;
    private final JavaExecutionOptions javaExecutionOptions;

    @Inject
    public InitializeRewriter(
            FileSystem fs,
            GlobalOptions globalOptions,
            KExceptionManager kem,
            SMTOptions smtOptions,
            KRunOptions krunOptions,
            KompileOptions kompileOptions,
            JavaExecutionOptions javaExecutionOptions,
            FileUtil files,
            InitializeDefinition initializeDefinition,
            Stopwatch sw,
            Profiler2 profiler) {
        this.fs = fs;
        this.sw = sw;
        this.globalOptions = globalOptions;
        this.kem = kem;
        this.smtOptions = smtOptions;
        this.hookProvider = HookProvider.get(kem);
        this.transitions = kompileOptions.transition;
        this.krunOptions = krunOptions;
        this.kompileOptions = kompileOptions;
        this.javaExecutionOptions = javaExecutionOptions;
        this.files = files;
        this.initializeDefinition = initializeDefinition;
        this.profiler = profiler;
    }

    @Override
    public synchronized Rewriter apply(Module mainModule) {
        TermContext initializingContext = TermContext.builder(new GlobalContext(fs, globalOptions, krunOptions, javaExecutionOptions, kem, smtOptions, hookProvider, files, Stage.INITIALIZING, profiler))
                .freshCounter(0).build();
        Definition definition;
        definition = initializeDefinition.invoke(mainModule, kem, initializingContext.global());
        GlobalContext rewritingContext = new GlobalContext(fs, globalOptions, krunOptions, javaExecutionOptions, kem, smtOptions, hookProvider, files, Stage.REWRITING, profiler);
        rewritingContext.setDefinition(definition);

        return new SymbolicRewriterGlue(mainModule, definition, definition, transitions, initializingContext.getCounterValue(), rewritingContext, kem, files, kompileOptions, sw);
    }

    public static Rule transformFunction(Function<K, K> f, Rule r) {
        return Rule.apply(f.apply(r.body()), f.apply(r.requires()), f.apply(r.ensures()), r.att());
    }

    public static Rule transform(Function1<K, K> f, Rule r) {
        return Rule.apply(f.apply(r.body()), f.apply(r.requires()), f.apply(r.ensures()), r.att());
    }


    public static class SymbolicRewriterGlue implements Rewriter {

        public final Definition definition;
        public Definition miniKoreDefinition;
        public final Module module;
        private final long initCounterValue;
        public final GlobalContext rewritingContext;
        private final KExceptionManager kem;
        private final FileUtil files;
        private final List<String> transitions;
        private KompileOptions kompileOptions;
        private final Stopwatch sw;

        public SymbolicRewriterGlue(
                Module module,
                Definition definition,
                Definition miniKoreDefinition,
                List<String> transitions,
                long initCounterValue,
                GlobalContext rewritingContext,
                KExceptionManager kem,
                FileUtil files, KompileOptions kompileOptions,
                Stopwatch sw) {
            this.transitions = transitions;
            this.files = files;
            this.kompileOptions = kompileOptions;
            this.sw = sw;
            this.definition = definition;
            this.miniKoreDefinition = miniKoreDefinition;
            this.module = module;
            this.initCounterValue = initCounterValue;
            this.rewritingContext = rewritingContext;
            this.kem = kem;
        }

        @Override
        public RewriterResult execute(K k, Optional<Integer> depth) {
            rewritingContext.stateLog.open("execute-" + Integer.toString(Math.abs(k.hashCode())));
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
            ResolveSemanticCasts resolveCasts = new ResolveSemanticCasts(true);
            ExpandMacros macroExpander = new ExpandMacros(module, files, kompileOptions, false);
            termContext.setKOREtoBackendKILConverter(converter);
            Term backendKil = converter.convert(macroExpander.expand(resolveCasts.resolve(k))).evaluate(termContext);
            SymbolicRewriter rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);
            RewriterResult result = rewriter.rewrite(new ConstrainedTerm(backendKil, termContext), depth.orElse(-1));
            rewritingContext.stateLog.close();
            return result;
        }

        @Override
        public K match(K k, Rule rule) {
            return search(k, Optional.of(0), Optional.empty(), rule, SearchType.STAR);
        }


        @Override
        public K search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern, SearchType searchType) {
            rewritingContext.stateLog.open("search-" + Integer.toString(Math.abs(initialConfiguration.hashCode())));
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
            ResolveSemanticCasts resolveCasts = new ResolveSemanticCasts(true);
            ExpandMacros macroExpander = new ExpandMacros(module, files, kompileOptions, false);
            termContext.setKOREtoBackendKILConverter(converter);
            Term javaTerm = converter.convert(macroExpander.expand(resolveCasts.resolve(initialConfiguration))).evaluate(termContext);
            org.kframework.backend.java.kil.Rule javaPattern = converter.convert(Optional.empty(), transformFunction(JavaBackend::convertKSeqToKApply, pattern));
            SymbolicRewriter rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);
            K result = rewriter.search(javaTerm, javaPattern, bound.orElse(NEGATIVE_VALUE), depth.orElse(NEGATIVE_VALUE), searchType, termContext);
            rewritingContext.stateLog.close();
            return result;
        }


        public Tuple2<RewriterResult, K> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
            RewriterResult res = execute(k, depth);
            return Tuple2.apply(res, match(res.k(), rule));
        }

        @Override
        public K prove(Module mod) {
            //todo kompileOptions.global == null, but shouldn't
            if (rewritingContext.globalOptions.verbose) {
                rewritingContext.profiler.logParsingTime();
            }
            rewritingContext.stateLog.open("prove-" + Integer.toString(Math.abs(mod.hashCode())));
            List<Rule> rules = stream(mod.rules()).filter(r -> r.att().contains("specification")).collect(Collectors.toList());
            ProcessProofRules processProofRules = new ProcessProofRules(rules).invoke(rewritingContext, initCounterValue, module, definition);
            List<org.kframework.backend.java.kil.Rule> javaRules = processProofRules.getJavaRules();
            KOREtoBackendKIL converter = processProofRules.getConverter();
            TermContext termContext = processProofRules.getTermContext();
            List<org.kframework.backend.java.kil.Rule> allRules = javaRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            // rename all variables again to avoid any potential conflicts with the rules in the semantics
            javaRules = javaRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            SymbolicRewriter rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);

            if (rewritingContext.globalOptions.verbose) {
                rewritingContext.profiler.logInitTime();
            }
            List<ConstrainedTerm> proofResults = javaRules.stream()
                    .filter(r -> !r.att().contains(Attribute.TRUSTED_KEY))
                    .map(r -> {
                        ConstrainedTerm lhs = r.createLhsPattern(termContext);
                        ConstrainedTerm rhs = r.createRhsPattern();
                        termContext.setInitialVariables(lhs.variableSet());
                        if (rewritingContext.javaExecutionOptions.cacheFunctionsOptimized) {
                            JavaSymbolicObject.clearCache();
                        }
                        return rewriter.proveRule(r, lhs, rhs, allRules, kem);
                    })
                    .flatMap(List::stream)
                    .collect(Collectors.toList());

            K result = proofResults.stream()
                    .map(ConstrainedTerm::term)
                    .map(t -> (KApply) t)
                    .reduce(((k1, k2) -> KApply(KLabels.ML_AND, k1, k2))).orElse(KApply(KLabels.ML_TRUE));
            rewritingContext.stateLog.close();
            return result;
        }

        @Override
        public boolean equivalence(Rewriter firstDef, Rewriter secondDef, Module firstSpec, Module secondSpec) {
            if (!(firstDef instanceof SymbolicRewriterGlue) || !(secondDef instanceof SymbolicRewriterGlue)) {
                throw KEMException.criticalError("All three definitions must be compiled with --backend java in order" +
                        "to check program equivalence.");
            }
            SymbolicRewriterGlue glue1 = (SymbolicRewriterGlue) firstDef;
            SymbolicRewriterGlue glue2 = (SymbolicRewriterGlue) secondDef;
            EquivalenceState state1 = new EquivalenceState(glue1, firstSpec);
            EquivalenceState state2 = new EquivalenceState(glue2, secondSpec);

            java.util.List<ConjunctiveFormula> startEnsures = new ArrayList<>();
            assert state1.startEnsures.size() == state2.startEnsures.size();
            for (int i = 0; i < state1.startEnsures.size(); i++) {
                startEnsures.add(getConjunctiveFormula(state1.startEnsures.get(i), state2.startEnsures.get(i), rewritingContext));
            }

            java.util.List<ConjunctiveFormula> targetEnsures = new ArrayList<>();
            assert state1.targetEnsures.size() == state2.targetEnsures.size();
            for (int i = 0; i < state1.targetEnsures.size(); i++) {
                targetEnsures.add(getConjunctiveFormula(state1.targetEnsures.get(i), state2.targetEnsures.get(i), rewritingContext));
            }

            return EquivChecker.equiv(
                    state1.startSyncNodes, state2.startSyncNodes,
                    state1.targetSyncNodes, state2.targetSyncNodes,
                    startEnsures, //info1.startEnsures, info2.startEnsures,
                    targetEnsures, //info1.targetEnsures, info2.targetEnsures,
                    state1.trusted, state2.trusted,
                    state1.rewriter, state2.rewriter);
        }

        private static ConjunctiveFormula getConjunctiveFormula(ConjunctiveFormula e1, ConjunctiveFormula e2, GlobalContext global) {

            ConjunctiveFormula ensure = ConjunctiveFormula.of(global);

            ImmutableList<Term> l1 = getChildren(e1);
            ImmutableList<Term> l2 = getChildren(e2);

            assert l1.size() == l2.size();
            for (int j = 0; j < l1.size(); j++) {
                // TODO: make it better
                ensure = ensure.add(
                        ((KList) ((KItem) l1.get(j)).kList()).getContents().get(0),
                        ((KList) ((KItem) l2.get(j)).kList()).getContents().get(0));
            }

            return ensure;
        }

        private static ImmutableList<Term> getChildren(ConjunctiveFormula e) {
            // TODO: make it better
            assert e.equalities().size() == 1;
            assert e.equalities().get(0).leftHandSide() instanceof KItem;
            assert ((KItem) e.equalities().get(0).leftHandSide()).kLabel() instanceof KLabelConstant;
            assert ((KLabelConstant) ((KItem) e.equalities().get(0).leftHandSide()).kLabel()).label().equals("vars");
            assert ((KItem) e.equalities().get(0).leftHandSide()).kList() instanceof KList;
            assert ((KList) ((KItem) e.equalities().get(0).leftHandSide()).kList()).getContents().size() == 1;
            assert ((KList) ((KItem) e.equalities().get(0).leftHandSide()).kList()).getContents().get(0) instanceof BuiltinList;

            return ((BuiltinList) ((KList) ((KItem) e.equalities().get(0).leftHandSide()).kList()).getContents().get(0)).children;
        }

        static class ProcessProofRules {
            private List<Rule> rules;
            private TermContext termContext;
            private KOREtoBackendKIL converter;
            private List<org.kframework.backend.java.kil.Rule> javaRules;

            public ProcessProofRules(List<Rule> rules) {
                this.rules = rules;
            }

            public TermContext getTermContext() {
                return termContext;
            }

            public KOREtoBackendKIL getConverter() {
                return converter;
            }

            public List<org.kframework.backend.java.kil.Rule> getJavaRules() {
                return javaRules;
            }

            public ProcessProofRules invoke(GlobalContext rewritingContext, long initCounterValue, Module module, Definition definition) {
                termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
                converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
                termContext.setKOREtoBackendKILConverter(converter);
                javaRules = rules.stream()
                        .map(r -> converter.convert(Optional.<Module>empty(), r))
                        .map(this::evaluateRule)
                        .collect(Collectors.toList());
                return this;
            }

            public org.kframework.backend.java.kil.Rule evaluateRule(org.kframework.backend.java.kil.Rule rule) {
                termContext.setTopConstraint(null);
                //We need this ConsTerm only to evaluate the constraint. That's why we use an empty first argument.
                ConstrainedTerm constraintHolder = new ConstrainedTerm(
                        ConjunctiveFormula.of(termContext.global()),
                        rule.getRequires(),
                        termContext).expandPatterns(true);

                ConjunctiveFormula constraint = constraintHolder.constraint();
                termContext.setTopConstraint(constraint);
                //simplify the constraint in its own context, to force full evaluation of terms.
                constraint = constraint.simplify(termContext);

                return new org.kframework.backend.java.kil.Rule(
                        rule.label(),
                        evaluate(rule.leftHandSide(), constraint, termContext),
                        evaluate(rule.rightHandSide(), constraint, termContext),
                        rule.requires(),
                        rule.ensures(),
                        rule.freshConstants(),
                        rule.freshVariables(),
                        rule.lookups(),
                        rule.att(),
                        termContext.global());
            }

            private Term evaluate(Term term, ConjunctiveFormula constraint, TermContext context) {
                context.setTopConstraint(constraint);
                return term.fullSubstituteAndEvaluate(context);
            }
        }
    }

    static class EquivalenceState {
        final List<ConstrainedTerm> startSyncNodes;
        final List<ConstrainedTerm> targetSyncNodes;
        final List<ConjunctiveFormula> startEnsures;
        final List<ConjunctiveFormula> targetEnsures;
        final List<Boolean> trusted;
        final SymbolicRewriter rewriter;

        EquivalenceState(SymbolicRewriterGlue glue, Module spec) {
            GlobalOptions globalOptions = glue.rewritingContext.globalOptions;
            FileUtil files = glue.files;
            KExceptionManager kem = glue.kem;
            Stopwatch sw = glue.sw;
            KompileOptions options = glue.kompileOptions;

            List<Rule> rules = stream(spec.rules()).filter(r -> r.att().contains("specification")).collect(Collectors.toList());

            SymbolicRewriterGlue.ProcessProofRules processProofRules = new SymbolicRewriterGlue.ProcessProofRules(rules);
            processProofRules.invoke(glue.rewritingContext, glue.initCounterValue, glue.module, glue.definition);

            List<org.kframework.backend.java.kil.Rule> specRules = processProofRules.javaRules;
            java.util.Collections.sort(specRules, new Comparator<org.kframework.backend.java.kil.Rule>() {
                @Override
                public int compare(org.kframework.backend.java.kil.Rule rule1, org.kframework.backend.java.kil.Rule rule2) {
                    return Integer.compare(rule1.getLocation().startLine(), rule2.getLocation().startLine());
                }
            });

            // rename all variables again to avoid any potential conflicts with the rules in the semantics
            specRules = specRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            // rename all variables again to avoid any potential conflicts with the rules in the semantics
            List<org.kframework.backend.java.kil.Rule> targetSpecRules = specRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            //// prove spec rules
            rewriter = new SymbolicRewriter(glue.rewritingContext, glue.transitions, processProofRules.converter);
            assert (specRules.size() == targetSpecRules.size());

            startSyncNodes = new ArrayList<>();
            targetSyncNodes = new ArrayList<>();
            startEnsures = new ArrayList<>();
            targetEnsures = new ArrayList<>();
            trusted = new ArrayList<>();

            for (int i = 0; i < specRules.size(); i++) {
                org.kframework.backend.java.kil.Rule startRule = specRules.get(i);
                org.kframework.backend.java.kil.Rule targetRule = targetSpecRules.get(i);

                // assert rule1.getEnsures().equals(rule2.getEnsures());

                // TODO: split requires for each side and for both sides in createLhsPattern
                startSyncNodes.add(startRule.createLhsPattern(processProofRules.termContext));
                targetSyncNodes.add(targetRule.createLhsPattern(processProofRules.termContext));
                startEnsures.add(startRule.getEnsures());
                targetEnsures.add(targetRule.getEnsures());

                // assert rule1.containsAttribute(Attribute.TRUSTED_KEY) == rule2.containsAttribute(Attribute.TRUSTED_KEY);
                trusted.add(startRule.att().contains(Attribute.TRUSTED_KEY));
            }
        }
    }


    public static class InitializeDefinition {

        private final Map<Module, Definition> cache = new LinkedHashMap<Module, Definition>() {
            @Override
            protected boolean removeEldestEntry(Map.Entry<Module, Definition> eldest) {
                return this.size() > 20;
            }
        };

        public Definition invoke(Module module, KExceptionManager kem, GlobalContext global) {
            if (cache.containsKey(module)) {
                return cache.get(module);
            }
            Definition definition = new Definition(module, kem);

            global.setDefinition(definition);

            JavaConversions.setAsJavaSet(module.attributesFor().keySet()).stream()
                    .map(l -> KLabelConstant.of(l, definition))
                    .forEach(definition::addKLabel);
            definition.addKoreRules(module, global);
            cache.put(module, definition);
            return definition;
        }
    }
}
