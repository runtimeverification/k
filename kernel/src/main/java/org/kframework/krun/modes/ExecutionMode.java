// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import org.kframework.rewriter.Rewriter;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;

/**
 * Created by Manasvi on 6/16/15.
 *
 * Interface for KRun Execution Modes.
 */
public interface ExecutionMode<T> {

    public T execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition);
}
