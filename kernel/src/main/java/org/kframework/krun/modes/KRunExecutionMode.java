package org.kframework.krun.modes;

import com.google.inject.Inject;
import org.kframework.ExecutionMode;
import org.kframework.Rewriter;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;

/**
 * Execution Mode for Conventional KRun
 */
public class KRunExecutionMode implements ExecutionMode<K> {

    private KRunOptions kRunOptions;

    @Inject
    public KRunExecutionMode(KRunOptions kRunOptions) {
        kRunOptions = kRunOptions;
    }

    @Override
    public K execute(K k, Rewriter rewriter) {
        return null;
    }
}
