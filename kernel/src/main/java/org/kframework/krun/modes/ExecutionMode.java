package org.kframework.krun.modes;

import org.kframework.Rewriter;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;

/**
 * Created by manasvi on 6/16/15.
 */
public interface ExecutionMode<T> {

    public T execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition);
}
