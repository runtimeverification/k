// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRun;
import org.kframework.rewriter.Rewriter;
import scala.Tuple2;

import java.util.function.Function;

/**
 * Created by Manasvi on 6/16/15.
 *
 * Interface for KRun Execution Modes.
 */
public interface ExecutionMode {

    Tuple2<K, Integer> execute(KRun.InitialConfiguration k, Function<Module, Rewriter> rewriter, CompiledDefinition compiledDefinition);
}
