// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.RewriterResult;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kore.ADT;
import org.kframework.kore.AbstractKORETransformer;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KCollection;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.TransformKORE;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;


/**
 * Class that implements the "--prove" option.
 */
public class ProofExecutionMode implements ExecutionMode<List<K>> {

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
    public List<K> execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        String proofFile = options.experimental.prove;
        Kompile kompile = new Kompile(compiledDefinition.kompileOptions, globalOptions, files, kem, sw, false);
        Module mod = kompile.parseModule(compiledDefinition, files.resolveWorkingDirectory(proofFile).getAbsoluteFile(), true);
        RewriterResult executionResult = rewriter.execute(k, Optional.<Integer>empty());

        ConfigurationInfo configurationInfo = new ConfigurationInfoFromModule(compiledDefinition.executionModule());
        AbstractKORETransformer<Map<String, K>> cellPlaceholderSubstitutionCollector = new AbstractKORETransformer<Map<String, K>>() {
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

        TransformKORE cellPlaceholderSubstitutionApplication = new TransformKORE() {
            @Override
            public K apply(KVariable k) {
                return cellPlaceholderSubstitution.getOrDefault(k.name(), k);
            }
        };

        List<Rule> rules = stream(mod.localRules())
                .map(r -> new Rule(
                        cellPlaceholderSubstitutionApplication.apply(r.body()),
                        cellPlaceholderSubstitutionApplication.apply(r.requires()),
                        cellPlaceholderSubstitutionApplication.apply(r.ensures()),
                        r.att()))
                .map(r -> kompile.compileRule(compiledDefinition, r))
                .collect(Collectors.toList());
        return rewriter.prove(rules);
    }
}
