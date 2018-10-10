// Copyright (c) 2018 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework;

import java.util.ArrayList;
import org.kframework.kore.K;


public class EvaluationException extends RuntimeException {
    private int steps_;
    private ArrayList<K> stacktrace_;

    public EvaluationException(int steps, ArrayList<K> stacktrace) {
        super("EvaluationException");
        steps_ = steps;
        stacktrace_ = stacktrace;
    }

    public int steps() { return steps_; }
    public ArrayList<K> stacktrace() { return stacktrace_; }
}
