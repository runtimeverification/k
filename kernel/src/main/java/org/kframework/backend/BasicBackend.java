// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend;

import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.Stopwatch;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12 Time: 11:18 PM
 */
public abstract class BasicBackend implements Backend {
    protected Stopwatch sw;
    protected Context context;
    protected KompileOptions options;

    public BasicBackend(Stopwatch sw, Context context) {
        this.sw = sw;
        this.context = context;
        this.options = context.kompileOptions;
    }

    @Override
    public Definition lastStep(Definition def) {
        return def;
    }

    @Override
    public Definition firstStep(Definition def) {
        return def;
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        steps.add(new FirstStep(this, context));
        return steps;
    }

    @Override
    public boolean autoinclude() {
        return !options.experimental.noPrelude;
    }

    @Override
    public String autoincludedFile() {
        return Backends.AUTOINCLUDE;
    }
}
