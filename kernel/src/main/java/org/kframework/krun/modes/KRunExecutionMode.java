// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
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
        if (kRunOptions.exitCodePattern != null) {
            Rule pattern = KRun.pattern(files, kem, kRunOptions.exitCodePattern, kRunOptions, compiledDefinition, Source.apply("<command line: --exit-code>"));
            Tuple2<K, List<Map<KVariable, K>>> res = rewriter.executeAndMatch(k, Optional.ofNullable(kRunOptions.depth), pattern);
            return Tuple2.apply(res._1(), KRun.getExitCode(kem, res._2()));
        }
        return rewriter.execute(k, Optional.ofNullable(kRunOptions.depth));
    }
}
