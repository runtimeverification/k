// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.rewriter.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.SearchResult;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.List;
import java.util.Map;
import java.util.Optional;


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
    public Object execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        Rule pattern = null, parsedPattern = null;
        if (kRunOptions.pattern != null) {
            parsedPattern = KRun.parsePattern(files, kem, kRunOptions.pattern, compiledDefinition, Source.apply("<command line>"));
            pattern = KRun.compilePattern(files, kem, kRunOptions.pattern, kRunOptions, compiledDefinition, Source.apply("<command line>"));
        }
        if (kRunOptions.search()) {
            if (pattern == null) {
                pattern = new Rule(KORE.KVariable("X"), BooleanUtils.TRUE, BooleanUtils.TRUE, KORE.Att());
                parsedPattern = pattern;
            }
            return new SearchResult(rewriter.search(k, Optional.ofNullable(kRunOptions.depth), Optional.ofNullable(kRunOptions.bound), pattern, kRunOptions.searchType()), parsedPattern);
        }
        if (kRunOptions.exitCodePattern != null) {
            Rule exitCodePattern = KRun.compilePattern(files, kem, kRunOptions.exitCodePattern, kRunOptions, compiledDefinition, Source.apply("<command line: --exit-code>"));
            Tuple2<RewriterResult, List<? extends Map<? extends KVariable, ? extends K>>> res;
            if (pattern != null) {
                res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), pattern);
                return new Tuple2<>(new SearchResult(res._2(), parsedPattern), KRun.getExitCode(kem, rewriter.match(res._1().k(), exitCodePattern)));
            }
            res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), exitCodePattern);
            return Tuple2.apply(res._1().k(), KRun.getExitCode(kem, res._2()));
        }
        if (pattern != null) {
            Tuple2<RewriterResult, List<? extends Map<? extends KVariable, ? extends K>>> res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), pattern);
            return new SearchResult(res._2(), parsedPattern);
        }
        return rewriter.execute(k, Optional.ofNullable(kRunOptions.depth)).k();
    }
}
