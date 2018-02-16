// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.attributes.Att;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.NormalizeKSeq;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.ADT;
import org.kframework.kore.AbstractKTransformer;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KCollection;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Function1;
import scala.Tuple2;
import scala.collection.Set;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;


/**
 * Class that implements the "--prove" option.
 */
public class ProofExecutionMode implements ExecutionMode<Tuple2<K, Integer>> {

    private final KExceptionManager kem;
    private final KRunOptions options;
    private final Stopwatch sw;
    private final FileUtil files;
    private final GlobalOptions globalOptions;

    @Inject
    public ProofExecutionMode(KExceptionManager kem, KRunOptions options, Stopwatch sw, FileUtil files, GlobalOptions globalOptions) {
        this.kem = kem;
        this.options = options;
        this.sw = sw;
        this.files = files;
        this.globalOptions = globalOptions;
    }

    @Override
    public Tuple2<K, Integer> execute(KRun.InitialConfiguration config, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        String proofFile = options.experimental.prove;
        Module mod = getProofModule(compiledDefinition, proofFile, globalOptions, files, kem, sw);
        K k = config.theConfig;
        config.theConfig = null;
        RewriterResult executionResult = rewriter.execute(k, Optional.<Integer>empty());

        ConfigurationInfo configurationInfo = new ConfigurationInfoFromModule(compiledDefinition.executionModule());
        AbstractKTransformer<Map<String, K>> cellPlaceholderSubstitutionCollector = new AbstractKTransformer<Map<String, K>>() {
            @Override
            public Map<String, K> apply(KApply k) {
                Map<String, K> substitution = processChildren(k.klist());
                if (configurationInfo.isCellLabel(new ADT.KLabel(k.klabel().name())) && k.klist().size() == 1) {
                    substitution = mergeSubstitutions(Stream.of(
                            substitution,
                            Collections.singletonMap(k.klabel().name().substring(1, k.klabel().name().length() - 1).toUpperCase().replace("-", ""), k.klist().items().get(0))));
                }
                return substitution;
            }

            @Override
            public Map<String, K> apply(KRewrite k) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Map<String, K> apply(KToken k) {
                return Collections.emptyMap();
            }

            @Override
            public Map<String, K> apply(InjectedKLabel k) {
                return Collections.emptyMap();
            }

            @Override
            public Map<String, K> apply(KAs k) {
                return mergeSubstitutions(Stream.of(k.pattern(), k.alias()).map(this::apply));
            }

            @Override
            public Map<String, K> apply(KVariable k) {
                return Collections.emptyMap();
            }

            @Override
            public Map<String, K> apply(KSequence k) {
                return processChildren(k);
            }

            private Map<String, K> processChildren(KCollection k) {
                return mergeSubstitutions(k.stream().map(this::apply));
            }

            private Map<String, K> mergeSubstitutions(Stream<Map<String, K>> stream) {
                return stream
                        .map(Map::entrySet)
                        .flatMap(Collection::stream)
                        .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue, (v1, v2) -> null));
            }
        };
        Map<String, K> cellPlaceholderSubstitution = cellPlaceholderSubstitutionCollector.apply(executionResult.k()).entrySet().stream()
                .filter(e -> e.getValue() != null)
                .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));

        TransformK cellPlaceholderSubstitutionApplication = new TransformK() {
            @Override
            public K apply(KVariable k) {
                return cellPlaceholderSubstitution.getOrDefault(k.name(), k);
            }
        };


        ExpandMacros macroExpander = new ExpandMacros(compiledDefinition.kompiledDefinition.mainModule(), kem, files, globalOptions, compiledDefinition.kompileOptions);

        List<Rule> rules = stream(mod.localRules())
                .filter(r -> r.toString().contains("spec.k"))
                .map(r -> new Rule(
                        cellPlaceholderSubstitutionApplication.apply(r.body()),
                        cellPlaceholderSubstitutionApplication.apply(r.requires()),
                        cellPlaceholderSubstitutionApplication.apply(r.ensures()),
                        r.att()))
                .map(r -> (Rule) macroExpander.expand(r))
                .map(r -> transformFunction(JavaBackend::ADTKVariableToSortedVariable, r))
                .map(r -> transformFunction(JavaBackend::convertKSeqToKApply, r))
                .map(r -> transform(NormalizeKSeq.self(), r))
                //.map(r -> kompile.compileRule(compiledDefinition, r))
                .collect(Collectors.toList());
        K results = rewriter.prove(rules);
        int exit;
        if (results instanceof KApply) {
            KApply kapp = (KApply) results;
            exit = kapp.klabel().name().equals("#True") ? 0 : 1;
        } else {
            exit = 1;
        }
        return Tuple2.apply(results, exit);
    }

    static Module getProofModule(CompiledDefinition compiledDefinition, String proofFile, GlobalOptions globalOptions, FileUtil files, KExceptionManager kem, Stopwatch sw) {
        Kompile kompile = new Kompile(compiledDefinition.kompileOptions, globalOptions, files, kem, sw, false);
        Module mod = kompile.parseModule(compiledDefinition, files.resolveWorkingDirectory(proofFile).getAbsoluteFile());

        Set<Module> alsoIncluded = Stream.of("K-TERM", "K-REFLECTION", RuleGrammarGenerator.ID_PROGRAM_PARSING)
                .map(module -> compiledDefinition.getParsedDefinition().getModule(module).get())
                .collect(org.kframework.Collections.toSet());

        mod = new JavaBackend(kem, files, globalOptions, compiledDefinition.kompileOptions)
                .stepsForProverRules()
                .apply(Definition.apply(mod, org.kframework.Collections.add(mod, alsoIncluded), Att.empty()))
                .getModule(mod.name()).get();
        return mod;
    }

    public static Rule transformFunction(Function<K, K> f, Rule r) {
        return Rule.apply(f.apply(r.body()), f.apply(r.requires()), f.apply(r.ensures()), r.att());
    }

    public static Rule transform(Function1<K, K> f, Rule r) {
        return Rule.apply(f.apply(r.body()), f.apply(r.requires()), f.apply(r.ensures()), r.att());
    }


}
