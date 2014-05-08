// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import org.kframework.kil.loader.Context;

public class KRunResult<T> {
    private String statistics;
    private String rawOutput;
    private T result;
    
    private Context context;

    public KRunResult(T result, Context context) {
        this.result = result;
        this.context = context;
    }

    public String getStatistics() {
        return statistics;
    }

    public void setStatistics(String statistics) {
        this.statistics = statistics;
    }

    public String getRawOutput() {
        return rawOutput;
    }

    public void setRawOutput(String rawOutput) {
        this.rawOutput = rawOutput;
    }

    public T getResult() {
        return result;
    }

    public void setResult(T result) {
        this.result = result;
    }

    @Override
    public String toString() {
        if (!context.krunOptions.experimental.statistics) {
            return result.toString();
        } else {
            return result.toString() + "\n" + statistics;
        }
    }
}
