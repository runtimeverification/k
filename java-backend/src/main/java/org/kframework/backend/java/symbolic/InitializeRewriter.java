// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.HookProvider;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;
import scala.Tuple2;
import scala.collection.JavaConversions;

import java.lang.invoke.MethodHandle;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by dwightguth on 5/6/15.
 */
public class InitializeRewriter implements Function<Module, Rewriter> {

    private final FileSystem fs;
    private final boolean deterministicFunctions;
    private final GlobalOptions globalOptions;
    private final KExceptionManager kem;
    private final SMTOptions smtOptions;
    private final Map<String, MethodHandle> hookProvider;
    private final List<String> transitions;
    private final KRunOptions krunOptions;
    private final FileUtil files;
    private final InitializeDefinition initializeDefinition;
    private static final int NEGATIVE_VALUE = -1;

    @Inject
    public InitializeRewriter(
            FileSystem fs,
            GlobalOptions globalOptions,
            KExceptionManager kem,
            SMTOptions smtOptions,
            KRunOptions krunOptions,
            KompileOptions kompileOptions,
            FileUtil files,
            InitializeDefinition initializeDefinition) {
        this.fs = fs;
        this.deterministicFunctions = false;
        this.globalOptions = globalOptions;
        this.kem = kem;
        this.smtOptions = smtOptions;
        this.hookProvider = HookProvider.get(kem);
        this.transitions = kompileOptions.transition;
        this.krunOptions = krunOptions;
        this.files = files;
        this.initializeDefinition = initializeDefinition;
    }

    @Override
    public synchronized Rewriter apply(Module mainModule) {
        TermContext initializingContext = TermContext.builder(new GlobalContext(fs, deterministicFunctions, globalOptions, krunOptions, kem, smtOptions, hookProvider, files, Stage.INITIALIZING))
                .freshCounter(0).build();
        Definition definition;
        definition = initializeDefinition.invoke(mainModule, kem, initializingContext.global());
        GlobalContext rewritingContext = new GlobalContext(fs, deterministicFunctions, globalOptions, krunOptions, kem, smtOptions, hookProvider, files, Stage.REWRITING);
        rewritingContext.setDefinition(definition);

        return new SymbolicRewriterGlue(mainModule, definition, definition, transitions, initializingContext.getCounterValue(), rewritingContext, kem);
    }

    public static class SymbolicRewriterGlue implements Rewriter {

        private SymbolicRewriter rewriter;
        public final Definition definition;
        public Definition miniKoreDefinition;
        public final Module module;
        private final BigInteger initCounterValue;
        public final GlobalContext rewritingContext;
        private final KExceptionManager kem;
        private final List<String> transitions;

        public SymbolicRewriterGlue(
                Module module,
                Definition definition,
                Definition miniKoreDefinition,
                List<String> transitions,
                BigInteger initCounterValue,
                GlobalContext rewritingContext,
                KExceptionManager kem) {
            this.transitions = transitions;
            this.rewriter = null;
            this.definition = definition;
            this.miniKoreDefinition = miniKoreDefinition;
            this.module = module;
            this.initCounterValue = initCounterValue;
            this.rewritingContext = rewritingContext;
            this.kem = kem;
        }

        @Override
        public RewriterResult execute(K k, Optional<Integer> depth) {
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
            termContext.setKOREtoBackendKILConverter(converter);
            Term backendKil = MacroExpander.expandAndEvaluate(termContext, kem, converter.convert(k));
            this.rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);
            RewriterResult result = rewriter.rewrite(new ConstrainedTerm(backendKil, termContext), depth.orElse(-1));
            return result;
        }

        @Override
        public List<? extends Map<? extends KVariable, ? extends K>> match(K k, Rule rule) {
            throw KEMException.criticalError("--search and --pattern are not implemented in --backend java");
            //return search(k, Optional.of(0), Optional.empty(), rule, SearchType.STAR, true);
        }


        @Override
        public List<? extends Map<? extends KVariable, ? extends K>> search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern, SearchType searchType) {
            throw KEMException.criticalError("--search and --pattern are not implemented in --backend java");
            //TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            //KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
            //termContext.setKOREtoBackendKILConverter(converter);
            //Term javaTerm = MacroExpander.expandAndEvaluate(termContext, kem, converter.convert(initialConfiguration));
            //org.kframework.backend.java.kil.Rule javaPattern = converter.convert(Optional.empty(), pattern);
            //this.rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);
            //return rewriter.search(javaTerm, javaPattern, bound.orElse(NEGATIVE_VALUE), depth.orElse(NEGATIVE_VALUE), searchType, termContext, resultsAsSubstitution);
        }


        public Tuple2<RewriterResult, List<? extends Map<? extends KVariable, ? extends K>>> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
            throw KEMException.criticalError("--search and --pattern are not implemented in --backend java");
            //RewriterResult res = execute(k, depth);
            //return Tuple2.apply(res, match(res.k(), rule));
        }

        @Override
        public List<K> prove(List<Rule> rules) {
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false);
            termContext.setKOREtoBackendKILConverter(converter);
            List<org.kframework.backend.java.kil.Rule> javaRules = rules.stream()
                    .map(r -> converter.convert(Optional.<Module>empty(), r))
                    .map(r -> new org.kframework.backend.java.kil.Rule(
                            r.label(),
                            r.leftHandSide().evaluate(termContext),
                            r.rightHandSide().evaluate(termContext),
                            r.requires(),
                            r.ensures(),
                            r.freshConstants(),
                            r.freshVariables(),
                            r.lookups(),
                            r.att(),
                            termContext.global()))
                    .collect(Collectors.toList());
            List<org.kframework.backend.java.kil.Rule> allRules = javaRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            // rename all variables again to avoid any potential conflicts with the rules in the semantics
            javaRules = javaRules.stream()
                    .map(org.kframework.backend.java.kil.Rule::renameVariables)
                    .collect(Collectors.toList());

            this.rewriter = new SymbolicRewriter(rewritingContext, transitions, converter);

            List<ConstrainedTerm> proofResults = javaRules.stream()
                    .filter(r -> !r.att().contains(Attribute.TRUSTED_KEY))
                    .map(r -> {
                        ConstrainedTerm lhs = r.createLhsPattern(termContext);
                        ConstrainedTerm rhs = r.createRhsPattern();
                        termContext.setInitialVariables(lhs.variableSet());
                        return rewriter.proveRule(lhs, rhs, allRules);
                    })
                    .flatMap(List::stream)
                    .collect(Collectors.toList());

            return proofResults.stream()
                    .map(ConstrainedTerm::term)
                    .map(t -> (KItem) t)
                    .collect(Collectors.toList());
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
                    .map(l -> KLabelConstant.of(l.name(), definition))
                    .forEach(definition::addKLabel);
            definition.addKoreRules(module, global);
            cache.put(module, definition);
            return definition;
        }
    }
}
