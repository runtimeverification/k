// Copyright (c) 2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework;

import java.util.List;
import org.kframework.kore.K;


public class EvaluationException extends RuntimeException {
    private int steps;
    private List<K> stacktrace;

    public EvaluationException(int steps, List<K> stacktrace) {
        super("Execution got stuck while evaluating a K function.");
        this.steps = steps;
        this.stacktrace = stacktrace;
    }

    public int steps() { return steps; }
    public List<K> stacktrace() { return stacktrace; }
}
