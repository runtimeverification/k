// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;

import java.util.Optional;

/**
 * Execution Mode for Conventional KRun
 */
public class KRunExecutionMode implements ExecutionMode<K> {

    private final KRunOptions kRunOptions;

    @Inject
    public KRunExecutionMode(KRunOptions kRunOptions) {
        this.kRunOptions = kRunOptions;
    }

    @Override
    public K execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        return rewriter.execute(k, Optional.ofNullable(kRunOptions.depth));
    }
}
