// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.RewriterResult;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.JavaKRunState;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Builtins;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.RequestScoped;
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
@RequestScoped
public class InitializeRewriter implements Function<Module, Rewriter> {

    private final FileSystem fs;
    private final JavaExecutionOptions javaOptions;
    private final GlobalOptions globalOptions;
    private final KExceptionManager kem;
    private final SMTOptions smtOptions;
    private final Map<String, Provider<MethodHandle>> hookProvider;
    private final KompileOptions kompileOptions;
    private final KRunOptions krunOptions;
    private final FileUtil files;
    private final InitializeDefinition initializeDefinition;
    private static final int NEGATIVE_VALUE = -1;

    @Inject
    public InitializeRewriter(
            FileSystem fs,
            JavaExecutionOptions javaOptions,
            GlobalOptions globalOptions,
            KExceptionManager kem,
            SMTOptions smtOptions,
            @Builtins Map<String, Provider<MethodHandle>> hookProvider,
            KompileOptions kompileOptions,
            KRunOptions krunOptions,
            FileUtil files,
            InitializeDefinition initializeDefinition) {
        this.fs = fs;
        this.javaOptions = javaOptions;
        this.globalOptions = globalOptions;
        this.kem = kem;
        this.smtOptions = smtOptions;
        this.hookProvider = hookProvider;
        this.kompileOptions = kompileOptions;
        this.krunOptions = krunOptions;
        this.files = files;
        this.initializeDefinition = initializeDefinition;
    }

    @Override
    public synchronized Rewriter apply(Module module) {
        TermContext initializingContext = TermContext.builder(new GlobalContext(fs, javaOptions, globalOptions, krunOptions, kem, smtOptions, hookProvider, files, Stage.INITIALIZING))
                .freshCounter(0).build();
        Definition evaluatedDef = initializeDefinition.invoke(module, kem, initializingContext.global());

        GlobalContext rewritingContext = new GlobalContext(fs, javaOptions, globalOptions, krunOptions, kem, smtOptions, hookProvider, files, Stage.REWRITING);
        rewritingContext.setDefinition(evaluatedDef);

        return new SymbolicRewriterGlue(module, evaluatedDef, kompileOptions, javaOptions, initializingContext.getCounterValue(), rewritingContext, kem);
    }

    public static class SymbolicRewriterGlue implements Rewriter {

        private final SymbolicRewriter rewriter;
        public final Definition definition;
        public final Module module;
        private final BigInteger initCounterValue;
        public final GlobalContext rewritingContext;
        private final KExceptionManager kem;

        public SymbolicRewriterGlue(
                Module module,
                Definition definition,
                KompileOptions kompileOptions,
                JavaExecutionOptions javaOptions,
                BigInteger initCounterValue,
                GlobalContext rewritingContext,
                KExceptionManager kem) {
            this.rewriter = new SymbolicRewriter(rewritingContext,  kompileOptions, javaOptions, new KRunState.Counter());
            this.definition = definition;
            this.module = module;
            this.initCounterValue = initCounterValue;
            this.rewritingContext = rewritingContext;
            this.kem = kem;
        }

        @Override
        public RewriterResult execute(K k, Optional<Integer> depth) {
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), false, false);
            Term backendKil = KILtoBackendJavaKILTransformer.expandAndEvaluate(termContext, kem, converter.convert(k));
            JavaKRunState result = (JavaKRunState) rewriter.rewrite(new ConstrainedTerm(backendKil, termContext), depth.orElse(-1));
            return new RewriterResult(result.getStepsTaken(), result.getJavaKilTerm());
        }

        @Override
        public List<? extends Map<? extends KVariable,? extends K>> match(K k, org.kframework.definition.Rule rule) {
            return search(k, Optional.of(0), Optional.empty(), rule, SearchType.STAR);
        }


        @Override
        public List<? extends Map<? extends KVariable, ? extends K>> search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern, SearchType searchType) {
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), true, false);
            Term javaTerm = KILtoBackendJavaKILTransformer.expandAndEvaluate(termContext, kem, converter.convert(initialConfiguration));
            org.kframework.backend.java.kil.Rule javaPattern = converter.convert(Optional.empty(), pattern);
            List<Substitution<Variable, Term>> searchResults;
            searchResults = rewriter.search(javaTerm, javaPattern, bound.orElse(NEGATIVE_VALUE), depth.orElse(NEGATIVE_VALUE),
                    searchType, termContext);
            return searchResults;
        }


        public Tuple2<RewriterResult, List<? extends Map<? extends KVariable, ? extends K>>> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
            RewriterResult res = execute(k, depth);
            return Tuple2.apply(res, match(res.k(), rule));
        }

        @Override
        public List<K> prove(List<Rule> rules) {
            TermContext termContext = TermContext.builder(rewritingContext).freshCounter(initCounterValue).build();
            KOREtoBackendKIL converter = new KOREtoBackendKIL(module, definition, termContext.global(), true, false);
            List<org.kframework.backend.java.kil.Rule> javaRules = rules.stream()
                    .map(r -> converter.convert(Optional.<Module>empty(), r))
                    .collect(Collectors.toList());
            List<org.kframework.backend.java.kil.Rule> allRules = javaRules.stream()
                    .map(r -> r.renameVariables())
                    .collect(Collectors.toList());

            List<ConstrainedTerm> proofResults = javaRules.stream()
                    .filter(r -> !r.containsAttribute(Attribute.TRUSTED_KEY))
                    .map(r -> rewriter.proveRule(r.createLhsPattern(termContext), r.createRhsPattern(), allRules))
                    .flatMap(List::stream)
                    .collect(Collectors.toList());

            return proofResults.stream()
                    .map(ConstrainedTerm::term)
                    .map(t -> (KItem) t)
                    .collect(Collectors.toList());
        }

    }


    @DefinitionScoped
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

            definition.setIndex(new IndexingTable(() -> definition, new IndexingTable.Data()));
            cache.put(module, definition);
            return definition;
        }
    }
}
