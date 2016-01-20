// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import org.kframework.kompile.CompiledDefinition;
import org.kframework.krun.KRun;
import org.kframework.rewriter.Rewriter;

/**
 * Created by Manasvi on 6/16/15.
 *
 * Interface for KRun Execution Modes.
 */
public interface ExecutionMode<T> {

    public T execute(KRun.InitialConfiguration k, Rewriter rewriter, CompiledDefinition compiledDefinition);
}
