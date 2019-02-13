// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Definition;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KORE;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.Optional;
import java.util.function.Function;


/**
 * Execution Mode for Conventional KRun
 */
public class KRunExecutionMode implements ExecutionMode {

    private final KRunOptions kRunOptions;
    private final KExceptionManager kem;
    private final FileUtil files;

    @Inject
    public KRunExecutionMode(KRunOptions kRunOptions, KExceptionManager kem, FileUtil files) {
        this.kRunOptions = kRunOptions;
        this.kem = kem;
        this.files = files;
    }

    @Override
    public Tuple2<K, Integer> execute(KRun.InitialConfiguration config, Function<Definition, Rewriter> rewriterGenerator, CompiledDefinition compiledDefinition) {
        Rewriter rewriter = rewriterGenerator.apply(compiledDefinition.kompiledDefinition);
        K k = config.theConfig;
        Rule pattern = null, parsedPattern = null;
        if (kRunOptions.pattern != null) {
            parsedPattern = KRun.parsePattern(files, kem, kRunOptions.pattern, compiledDefinition, Source.apply("<command line>"));
            pattern = KRun.compilePattern(files, kem, kRunOptions.pattern, compiledDefinition, Source.apply("<command line>"));
        }
        if (kRunOptions.search()) {
            if (pattern == null) {
                pattern = new Rule(KORE.KVariable("Result"), BooleanUtils.TRUE, BooleanUtils.TRUE, KORE.Att());
                parsedPattern = pattern;
            }
            return Tuple2.apply(rewriter.search(k, Optional.ofNullable(kRunOptions.depth), Optional.ofNullable(kRunOptions.bound), pattern, kRunOptions.searchType()), 0);
        }
        if (compiledDefinition.exitCodePattern != null) {
            Tuple2<RewriterResult, K> res;
            if (pattern != null) {
                res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), pattern);
                return new Tuple2<>(res._2(), KRun.getExitCode(kem, rewriter.match(res._1().k(), compiledDefinition.exitCodePattern)));
            }
            res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), compiledDefinition.exitCodePattern);
            return Tuple2.apply(res._1().k(), KRun.getExitCode(kem, res._2()));
        }
        if (pattern != null) {
            Tuple2<RewriterResult, K> res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), pattern);
            return Tuple2.apply(res._2(), 0);
        }
        RewriterResult res = rewriter.execute(k, Optional.ofNullable(kRunOptions.depth));
        return Tuple2.apply(res.k(), res.exitCode().orElse(0));
    }
}
